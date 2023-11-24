Require Import Kami.AllNotations.
Require Import ProcKami.Cheriot.Lib ProcKami.Cheriot.Types.
Require Import ProcKami.Cheriot.DecExec ProcKami.Cheriot.BankedMem.

Section Run.
  Context `{procParams: ProcParams}.
  Variable ty: Kind -> Type.
  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Variable uncompressFn: CompInst @# ty -> Maybe Inst ## ty.
  Variable funcEntries: list FuncEntry.
  Variable scrs: list ScrReg.
  Variable csrs: list CsrReg.

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

  Definition RegReadId := STRUCT_TYPE {
                              "cs1?" :: Bool;
                              "cs1Idx" :: RegId;
                              "cs2?" :: Bool;
                              "cs2Idx" :: RegId;
                              "scr?" :: Bool;
                              "scrIdx" :: Bit 5;
                              "csr?" :: Bool;
                              "csrIdx" :: Bit (snd immField) }.

  Definition RegReadIdOut := STRUCT_TYPE {
                                 "uncompressOut" :: UncompressOut;
                                 "allMatches" :: MatchFuncEntryStruct funcEntries;
                                 "regReadId" :: RegReadId }.

  Definition regReadId (uncompressOut: UncompressOut @# ty) :=
    ( LET inst <- uncompressOut @% "inst";
      LETAE allMatches <- matchFuncEntry #inst funcEntries;
      LET hasCs1Prop <- hasCs1PropFn #allMatches;
      LET hasCs2Prop <- hasCs2PropFn #allMatches;
      LET hasScrProp <- hasScrPropFn #allMatches;
      LET hasCsrProp <- hasCsrPropFn #allMatches;
      LET implicitReadVal <- implicitReadPropFn #allMatches;
      LET implicitReadProp <- isNotZero #implicitReadVal;
      LET implicitMepccProp <- implicitMepccPropFn #allMatches;
      LET implicitIeProp <- implicitIePropFn #allMatches;

      Ret (STRUCT { "uncompressOut" ::= uncompressOut;
                    "allMatches" ::= #allMatches;
                    "regReadId" ::=
                      (STRUCT { "cs1?" ::= (#hasCs1Prop || #implicitReadProp);
                                "cs1Idx" ::= ITE #implicitReadProp #implicitReadVal (rs1 #inst);
                                "cs2?" ::= #hasCs2Prop;
                                "cs2Idx" ::= rs2 #inst;
                                "scr?" ::= (#hasScrProp || #implicitMepccProp);
                                "scrIdx" ::= ITE #implicitMepccProp $$(implicitScrAddr scrs) (rs2Fixed #inst);
                                "csr?" ::= (#hasCsrProp || #implicitIeProp);
                                "csrIdx" ::= ITE #implicitIeProp $$(implicitCsrAddr csrs) (imm #inst) }
                        : RegReadId @# ty) } : RegReadIdOut @# ty ) ).

  Definition RegRead := STRUCT_TYPE {
                            "cs1" :: FullCapWithTag;
                            "cs2" :: FullCapWithTag;
                            "scr" :: FullCapWithTag;
                            "csr" :: Data }.

  Definition RegReadOut := STRUCT_TYPE {
                               "uncompressOut" :: UncompressOut;
                               "allMatches" :: MatchFuncEntryStruct funcEntries;
                               "regRead" :: RegRead }.

  Definition regReadNondet k (isRead: Bool @# ty) (val: ActionT ty k) :=
    ( If !isRead
      then ( Nondet rand: k;
             Ret #rand )
      else val
      as ret;
      Ret #ret ).

  Definition regReadSpec (regReadIdOut: RegReadIdOut @# ty) :=
    ( LET regReadId <- regReadIdOut @% "regReadId";
      LET cs1Idx <- #regReadId @% "cs1Idx";
      LET cs2Idx <- #regReadId @% "cs2Idx";
      LETA cs1 <- regReadNondet (#regReadId @% "cs1?")
                    ( If #cs1Idx == $0
                      then Ret (Const ty Default)
                      else callReadRegFile FullCapWithTag regsRead1 #cs1Idx as retVal;
                      Ret #retVal);
      LETA cs2 <- regReadNondet (#regReadId @% "cs2?")
                    ( If #cs2Idx == $0
                      then Ret (Const ty Default)
                      else callReadRegFile FullCapWithTag regsRead2 #cs2Idx as retVal;
                      Ret #retVal);
      LETA scr <- regReadNondet (#regReadId @% "scr?")
                    (readRegs procName (map scrRegInfo scrs) (#regReadId @% "scrIdx"));
      LETA csr <- regReadNondet (#regReadId @% "csr?")
                    (readRegs procName (map csrRegInfo csrs) (#regReadId @% "csrIdx"));
      Ret (STRUCT { "uncompressOut" ::= regReadIdOut @% "uncompressOut";
                    "allMatches" ::= regReadIdOut @% "allMatches";
                    "regRead" ::=
                      (STRUCT { "cs1" ::= #cs1;
                                "cs2" ::= #cs2;
                                "scr" ::= #scr;
                                "csr" ::= #csr } : RegRead @# ty) } : RegReadOut @# ty ) ).

  Definition regsFile :=
    {|rfIsWrMask := false;
      rfNum := 1;
      rfDataArray := regsArray;
      rfRead := Async [regsRead1; regsRead2];
      rfWrite := regsWrite;
      rfIdxNum := Nat.pow 2 RegIdSz;
      rfData := FullCapWithTag;
      rfInit := regsInit |}.

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
  
  Definition decode (regReadOut: RegReadOut @# ty) : ActionT ty DecodeOut :=
    ( LET uncompressOut <- regReadOut @% "uncompressOut";
      LET allMatches <- regReadOut @% "allMatches";
      LET regRead <- regReadOut @% "regRead";
      LET pc <- #uncompressOut @% "pc";
      LET inst <- #uncompressOut @% "inst";

      LETAE decodes : DecodeFuncEntryStruct funcEntries <-
                        decodeFuncEntry #pc #inst (#regRead @% "cs1") (#regRead @% "cs2")
                          (#regRead @% "scr") (#regRead @% "csr") #allMatches;
      
      Ret ((STRUCT { "pc" ::= #pc;
                     "inst" ::= #inst;
                     "badLower16?" ::= #uncompressOut @% "badLower16?";
                     "error?" ::= #uncompressOut @% "error?";
                     "fault?" ::= #uncompressOut @% "fault?";
                     "bounds?" ::= #uncompressOut @% "bounds?";
                     "legal?" ::= #uncompressOut @% "legal?";
                     "decodes" ::= #decodes }) : DecodeOut @# ty) ).

  Definition ExecOut := STRUCT_TYPE {
                            "pc" :: Addr;
                            "notCompressed?" :: Bool;
                            "result" :: FuncOutput;
                            "cdIdx" :: RegId;
                            "csrIdx" :: Bit (snd immField)
                          }.

  Definition getScrIdx (csrIdx: Bit (snd immField) @# ty) := UniBit (TruncLsb 5 _) csrIdx.
  
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
                     "result" ::= #newFuncOut;
                     "cdIdx" ::= rd #inst;
                     "csrIdx" ::= imm #inst } : ExecOut @# ty)) ).

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


(* TODO: Wb: Takes FuncOutput with memory updates, implicitly writes to PC and registers. *)
