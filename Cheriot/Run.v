Require Import Kami.AllNotations.
Require Import ProcKami.Cheriot.Types ProcKami.Cheriot.BankedMem ProcKami.Cheriot.DecExec ProcKami.Cheriot.CsrScr.

Section Run.
  Context `{procParams: ProcParams}.
  Variable ty: Kind -> Type.
  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Variable uncompressFn: CompInst @# ty -> Maybe Inst ## ty.
  Variable funcEntries: list FuncEntry.

  Definition FetchOut := STRUCT_TYPE {
                             "pc" :: FullCap;
                             "inst" :: Inst;
                             "badLower16?" :: Bool;
                             "error?" :: Bool;
                             "fault?" :: Bool;
                             "bounds?" :: Bool }.

  Definition fetch: ActionT ty FetchOut :=
    ( Read pcCap : Cap <- pcCapReg;
      Read pcVal : Addr <- pcValReg;
      LETA instRet <- instReq #pcVal;
      LET rawInst <- #instRet @% "inst";
      LET notCompressed <- isInstNotCompressed #rawInst;
      LETAE baseTop <- getCapBaseTop capAccessors #pcCap #pcVal;
      LET baseBound <- #pcVal >= (#baseTop @% "base");
      LET topBound <- ZeroExtend 1 #pcVal + (ITE #notCompressed $4 $2) <= (#baseTop @% "top");
      Ret ((STRUCT { "pc" ::= STRUCT { "cap" ::= #pcCap ; "val" ::= #pcVal } ;
                     "inst" ::= #rawInst;
                     "badLower16?" ::= #instRet @% "badLower16?";
                     "error?" ::= #instRet @% "error?";
                     "fault?" ::= #instRet @% "fault?";
                     "bounds?" ::= #baseBound && #topBound }): FetchOut @# ty )).

  Definition UncompressOut := STRUCT_TYPE {
                                  "pc" :: FullCap;
                                  "inst" :: Inst;
                                  "badLower16?" :: Bool;
                                  "error?" :: Bool;
                                  "fault?" :: Bool;
                                  "bounds?" :: Bool;
                                  "legal?" :: Bool }.

  Definition uncompressValid (fetchOut: FetchOut @# ty) : ActionT ty UncompressOut :=
    ( LET notCompressed <- isInstNotCompressed (fetchOut @% "inst");      
      LETAE maybeUncompressedInst <- uncompressFn (ZeroExtendTruncLsb CompInstSz (fetchOut @% "inst"));
      Ret ((STRUCT { "pc" ::= fetchOut @% "pc";
                     "inst" ::= ITE #notCompressed (fetchOut @% "inst") (#maybeUncompressedInst @% "data");
                     "badLower16?" ::= fetchOut @% "badLower16?";
                     "error?" ::= fetchOut @% "error?";
                     "fault?" ::= fetchOut @% "fault?";
                     "bounds?" ::= fetchOut @% "bounds?";
                     "legal?" ::= #maybeUncompressedInst @% "valid" }) : UncompressOut @# ty)).

  Definition uncompressInvalid (fetchOut: FetchOut @# ty) : ActionT ty UncompressOut :=
    ( LET notCompressed <- isInstNotCompressed (fetchOut @% "inst");
      Ret ((STRUCT { "pc" ::= fetchOut @% "pc";
                     "inst" ::= fetchOut @% "inst";
                     "badLower16?" ::= fetchOut @% "badLower16?";
                     "error?" ::= fetchOut @% "error?";
                     "fault?" ::= fetchOut @% "fault?";
                     "bounds?" ::= fetchOut @% "bounds?";
                     "legal?" ::= #notCompressed }) : UncompressOut @# ty)).

  Definition uncompress (fetchOut: FetchOut @# ty): ActionT ty UncompressOut :=
    if compressed
    then uncompressValid fetchOut
    else uncompressInvalid fetchOut.

  Definition regsFile :=
    {|rfIsWrMask := false;
      rfNum := 1;
      rfDataArray := regsArray;
      rfRead := Async [regsRead1; regsRead2];
      rfWrite := regsWrite;
      rfIdxNum := Nat.pow 2 RegIdSz;
      rfData := FullCapWithTag;
      rfInit := regsInit |}.

  Theorem XlenSXlenMinus1: Xlen = ((S (Xlen - 1)) * 1)%nat.
  Proof.
    destruct procParams as [xlen xlen_vars].
    destruct xlen_vars; subst; simpl; lia.
  Qed.

  Definition DecodeOut := STRUCT_TYPE {
                              "pc" :: FullCap;
                              "inst" :: Inst;
                              "badLower16?" :: Bool;
                              "error?" :: Bool;
                              "fault?" :: Bool;
                              "bounds?" :: Bool;
                              "legal?" :: Bool;
                              "decodes" :: DecodeFuncEntryStruct funcEntries
                            }.
  
  Definition regReadDecode (uncompressOut: UncompressOut @# ty) : ActionT ty DecodeOut :=
    ( LET pc <- uncompressOut @% "pc";
      LET inst <- uncompressOut @% "inst";
      LETAE allMatches <- matchFuncEntry #inst funcEntries;
      LET hasCs1Prop <- propertiesFuncEntry #allMatches hasCs1;
      LET hasCs2Prop <- propertiesFuncEntry #allMatches hasCs2;
      LET hasScrProp <- propertiesFuncEntry #allMatches hasScr;
      LET hasCsrProp <- propertiesFuncEntry #allMatches hasCsr;
      LET implicitReadProp <- propertiesFuncEntry #allMatches (fun p => Nat.eqb (implicit p) ImplicitRead);
      LET implicitMepccProp <- propertiesFuncEntry #allMatches implicitMepcc;
      LET implicitIeProp <- propertiesFuncEntry #allMatches implicitIe;

      LET getCs1Idx <- ITE #implicitReadProp $ImplicitRead (rs1 #inst);
      LET getCs2Idx <- rs2 #inst;
      LET getScrIdx <- ITE #implicitMepccProp $MepccAddr (rs2Fixed #inst);
      LET getCsrIdx <- imm #inst;

      LETA cs1 <- ( If !(#hasCs1Prop || #implicitReadProp)
                    then ( Nondet rand: FullCapWithTag;
                           Ret #rand )
                    else ( If #getCs1Idx == $0
                           then Ret (Const ty Default)
                           else callReadRegFile FullCapWithTag regsRead1 #getCs1Idx as retVal;
                           Ret #retVal ) as ret;
                    Ret #ret);

      LETA cs2 <- ( If !#hasCs2Prop
                    then ( Nondet rand: FullCapWithTag;
                           Ret #rand )
                    else ( If #getCs2Idx == $0
                           then Ret (Const ty Default)
                           else callReadRegFile FullCapWithTag regsRead2 #getCs2Idx as retVal;
                           Ret #retVal ) as ret;
                    Ret #ret);

      LETA scr <- ( If !(#hasScrProp || #implicitMepccProp)
                    then ( Nondet rand: FullCapWithTag;
                           Ret #rand)
                    else ( readRegs scrs FullCapWithTag #getScrIdx ) as retVal;
                    Ret #retVal );

      LETA csr <- ( If !#hasCsrProp
                    then ( Nondet rand: Data;
                           Ret #rand)
                    else ( readRegs csrs Data #getCsrIdx ) as retVal;
                    Ret #retVal );

      LETA ie <- ( If !#implicitIeProp
                   then ( Nondet rand: Bool;
                          Ret #rand)
                   else ( Read status : Bit Xlen <- procName ++ "_" ++ "mstatus";
                          LET statusArr <- (unpack (Array (S (Xlen-1)) Bool)
                                              (castBits XlenSXlenMinus1 #status));
                          Ret (#statusArr ![ 3 ]) ) as retVal;
                   Ret #retVal );

      LETAE decodes : DecodeFuncEntryStruct funcEntries <-
                        decodeFuncEntry #pc #inst #cs1 #cs2 #scr #csr #ie #allMatches;
      
      Ret ((STRUCT { "pc" ::= #pc;
                     "inst" ::= #inst;
                     "badLower16?" ::= uncompressOut @% "badLower16?";
                     "error?" ::= uncompressOut @% "error?";
                     "fault?" ::= uncompressOut @% "fault?";
                     "bounds?" ::= uncompressOut @% "bounds?";
                     "legal?" ::= uncompressOut @% "legal?";
                     "decodes" ::= #decodes }) : DecodeOut @# ty) ).

  Definition ExecOut := STRUCT_TYPE {
                            "pc" :: Addr;
                            "notCompressed?" :: Bool;
                            "result" :: FuncOutput
                          }.
  
  Definition exec (decodeOut: DecodeOut @# ty) : ActionT ty ExecOut :=
    ( LETAE funcOut : Maybe FuncOutput <- execFuncEntry (decodeOut @% "decodes");
      LET funcOutData <- #funcOut @% "data";
      LET pc <- decodeOut @% "pc" @% "val";
      LET inst <- decodeOut @% "inst";
      LET funcOutDataData <- #funcOutData @% "data";
      LET exception <- !(decodeOut @% "bounds?")
                       || (decodeOut @% "error?")
                       || (decodeOut @% "fault?")
                       || !(decodeOut @% "legal?")
                       || !(#funcOut @% "valid")
                       || (#funcOutData @% "exception?");
      LET exceptionCause : Data <-
                             ( IF !(decodeOut @% "bounds?")
                               then $CapBoundsViolation
                               else ( IF decodeOut @% "error?"
                                      then $InstAccessFault
                                      else ( IF decodeOut @% "fault?"
                                             then $InstPageFault
                                             else ( IF !(decodeOut @% "legal?") || !(#funcOut @% "valid")
                                                    then $InstIllegal
                                                    else #funcOutDataData @% "val" ))));
      LET baseException <- ( IF !(decodeOut @% "bounds?")
                             then $$false
                             else ( IF (decodeOut @% "error?") || (decodeOut @% "fault?") ||
                                      !(decodeOut @% "legal?") || !(#funcOut @% "valid")
                                    then $$true
                                    else #funcOutData @% "baseException?" ) );
      LET pcCapException <- ( IF !(decodeOut @% "bounds?")
                              then $$true
                              else #funcOutData @% "pcCapException?" );
      LET exceptionValue <- ( IF decodeOut @% "error?" || decodeOut @% "fault?"
                              then #pc + ITE (decodeOut @% "badLower16?") $0 $2
                              else ( IF !(decodeOut @% "legal?") || !(#funcOut @% "valid")
                                     then ZeroExtendTruncLsb CapSz #inst
                                     else #funcOutDataData @% "cap" ) );
      LET newFuncOut : FuncOutput <- #funcOutData
                          @%[ "exception?" <- #exception ]
                          @%[ "baseException?" <- #baseException ]
                          @%[ "pcCapException?" <- #pcCapException ]
                          @%[ "data" <- ((STRUCT {
                                              "tag" ::= #funcOutDataData @% "tag";
                                              "cap" ::= #exceptionValue;
                                              "val" ::= #exceptionCause }) : FullCapWithTag @# ty) ];
      Ret ((STRUCT { "pc" ::= #pc;
                     "notCompressed?" ::= isInstNotCompressed #inst;
                     "result" ::= #newFuncOut } : ExecOut @# ty)) ).

  Definition mem (execOut: ExecOut @# ty) : ActionT ty ExecOut :=
    ( LET funcOut : FuncOutput <- execOut @% "result";
      LET funcOutData : FullCapWithTag <- #funcOut @% "data";
      LET memInfo <- unpack MemOpInfo (ZeroExtendTruncLsb (size MemOpInfo)
                                         (#funcOut @% "pcOrScrCapOrMemOp"));
      If !(execOut @% "result" @% "exception?") && (#funcOut @% "mem?")
      then (
          LET isStore <- #memInfo @% "op" == $StOp;
          LETA memRet : DataRet <- loadStoreReq #isStore (#funcOut @% "addrOrScrOrCsrVal") (#memInfo @% "size")
                                     (#memInfo @% "cap?") (#funcOut @% "data") (#memInfo @% "sign?");
          LET isLoad <- !#isStore;
          LET memRetData <- #memRet @% "data";
          LET loadCap <- #memRetData @% "cap";
          LET loadTag <- #memRetData @% "tag";
          LETAE loadPerms <- getCapPerms capAccessors #loadCap;
          LET loadIsSealed <- isSealed capAccessors #loadCap;
          LET keepGL_LG <- !#loadTag || (#memInfo @% "LG");
          LET keepSD_LM <- !#loadTag || (#memInfo @% "LM") || #loadIsSealed;
          LET newLoadPerms <- #loadPerms
                                @%[ "GL" <- #keepGL_LG && (#loadPerms @% "GL") ]
                                @%[ "LG" <- #keepGL_LG && (#loadPerms @% "LG") ]
                                @%[ "SD" <- #keepSD_LM && (#loadPerms @% "SD") ]
                                @%[ "LM" <- #keepSD_LM && (#loadPerms @% "LM") ];
          LET newLoadTag <- (#memInfo @% "MC") && #loadTag;
          LETAE newLoadCap <- setCapPerms capAccessors #newLoadPerms #loadCap;
          LET exception <- (#memRet @% "dataError?") || (#memRet @% "dataFault?")
                           || (#memRet @% "tagError?") || (#memRet @% "tagFault?");
          LET newDataVal : Data <- ( IF #memRet @% "dataError?"
                                     then ITE #isStore $StoreAccessFault $LoadAccessFault
                                     else ( IF #memRet @% "dataFault?"
                                            then ITE #isStore $StorePageFault $LoadPageFault
                                            else ( IF #memRet @% "tagError?"
                                                   then $TagAccessFault
                                                   else ( IF #memRet @% "tagFault?"
                                                          then $TagPageFault
                                                          else (#memRetData @% "val")))));
          LET exceptionValue : Addr <- #funcOut @% "addrOrScrOrCsrVal" +
                                         ZeroExtendTruncLsb Xlen
                                           (ITE ((#memRet @% "dataError?") || (#memRet @% "dataFault?"))
                                              (#memRet @% "lowestByte")
                                              $0);
          (* TODO : Revocation *)
          LET newFuncOutData <- STRUCT {
                                    "tag" ::= #newLoadTag;
                                    "cap" ::= ITE #exception #exceptionValue #newLoadCap;
                                    "val" ::= #newDataVal };
          Ret (#funcOut @%[ "data" <- #newFuncOutData]
                 @%[ "exception?" <- #exception ]))
      else Ret #funcOut
      as retFuncOut;
      Ret (execOut @%[ "result" <- #retFuncOut ]) ).
End Run.


(* TODOs:
- Wb: Takes FuncOutput with memory updates, implicitly writes to PC and registers.
*)
