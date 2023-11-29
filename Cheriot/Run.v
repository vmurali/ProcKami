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
                             "justFenceI?" :: Bool;
                             "bounds?" :: Bool }.

  Definition instRetProcess (pcCap: Cap @# ty) (pcVal: Addr @# ty) (instRet : InstRet @# ty) : FetchOut ## ty :=
    ( LETC rawInst <- instRet @% "inst";
      LETC notCompressed <- isInstNotCompressed #rawInst;
      LETE baseTop <- getCapBaseTop capAccessors pcCap pcVal;
      LETC baseBound <- pcVal >= (#baseTop @% "base");
      LETC topBound <- ZeroExtend 1 pcVal + (ITE #notCompressed $4 $2) <= (#baseTop @% "top");
      RetE ((STRUCT { "pc" ::= STRUCT { "cap" ::= pcCap ; "val" ::= pcVal } ;
                      "inst" ::= #rawInst;
                      "badLower16?" ::= instRet @% "badLower16?";
                      "error?" ::= instRet @% "error?";
                      "fault?" ::= instRet @% "fault?";
                      "justFenceI?" ::= instRet @% "justFenceI?";
                      "bounds?" ::= #baseBound && #topBound }): FetchOut @# ty )).

  Definition fetchSpec: ActionT ty FetchOut :=
    ( Read pcCap : Cap <- pcCapReg;
      Read pcVal : Addr <- pcValReg;
      LETA instRet <- instReq #pcVal;
      convertLetExprSyntax_ActionT (instRetProcess #pcCap #pcVal #instRet) ).

  Definition UncompressOut := STRUCT_TYPE {
                                  "pc" :: FullCap;
                                  "inst" :: Inst;
                                  "badLower16?" :: Bool;
                                  "error?" :: Bool;
                                  "fault?" :: Bool;
                                  "justFenceI?" :: Bool;
                                  "bounds?" :: Bool;
                                  "legal?" :: Bool }.

  Definition uncompressValid (fetchOut: FetchOut @# ty) : UncompressOut ## ty :=
    ( LETC notCompressed <- isInstNotCompressed (fetchOut @% "inst");      
      LETE maybeUncompressedInst <- uncompressFn (ZeroExtendTruncLsb CompInstSz (fetchOut @% "inst"));
      RetE ((STRUCT { "pc" ::= fetchOut @% "pc";
                      "inst" ::= ITE #notCompressed (fetchOut @% "inst") (#maybeUncompressedInst @% "data");
                      "badLower16?" ::= fetchOut @% "badLower16?";
                      "error?" ::= fetchOut @% "error?";
                      "fault?" ::= fetchOut @% "fault?";
                      "justFenceI?" ::= fetchOut @% "justFenceI?";
                      "bounds?" ::= fetchOut @% "bounds?";
                      "legal?" ::= #maybeUncompressedInst @% "valid" }) : UncompressOut @# ty)).

  Definition uncompressInvalid (fetchOut: FetchOut @# ty) : UncompressOut ## ty :=
    ( LETC notCompressed <- isInstNotCompressed (fetchOut @% "inst");
      RetE ((STRUCT { "pc" ::= fetchOut @% "pc";
                      "inst" ::= fetchOut @% "inst";
                      "badLower16?" ::= fetchOut @% "badLower16?";
                      "error?" ::= fetchOut @% "error?";
                      "fault?" ::= fetchOut @% "fault?";
                      "justFenceI?" ::= fetchOut @% "justFenceI?";
                      "bounds?" ::= fetchOut @% "bounds?";
                      "legal?" ::= #notCompressed }) : UncompressOut @# ty)).

  Definition uncompress (fetchOut: FetchOut @# ty): UncompressOut ## ty :=
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
    ( LETC inst <- uncompressOut @% "inst";
      LETE allMatches <- matchFuncEntry #inst funcEntries;
      LETC hasCs1Prop <- hasCs1PropFn #allMatches;
      LETC hasCs2Prop <- hasCs2PropFn #allMatches;
      LETC hasScrProp <- hasScrPropFn #allMatches;
      LETC hasCsrProp <- hasCsrPropFn #allMatches;
      LETC implicitReadVal <- implicitReadPropFn #allMatches;
      LETC implicitReadProp <- isNotZero #implicitReadVal;
      LETC implicitMepccProp <- implicitMepccPropFn #allMatches;
      LETC implicitIeProp <- implicitIePropFn #allMatches;

      RetE (STRUCT { "uncompressOut" ::= uncompressOut;
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

  Let scrRegInfos := map scrRegInfo scrs.
  Let csrRegInfos := map csrRegInfo csrs.
  
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
                    (readRegs procName scrRegInfos (#regReadId @% "scrIdx"));
      LETA csr <- regReadNondet (#regReadId @% "csr?")
                    (readRegs procName csrRegInfos (#regReadId @% "csrIdx"));
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
                              "justFenceI?" :: Bool;
                              "bounds?" :: Bool;
                              "legal?" :: Bool;
                              "decodes" :: DecodeFuncEntryStruct funcEntries
                            }.
  
  Definition decode (regReadOut: RegReadOut @# ty) : DecodeOut ## ty :=
    ( LETC uncompressOut <- regReadOut @% "uncompressOut";
      LETC allMatches <- regReadOut @% "allMatches";
      LETC regRead <- regReadOut @% "regRead";
      LETC pc <- #uncompressOut @% "pc";
      LETC inst <- #uncompressOut @% "inst";

      LETE decodes : DecodeFuncEntryStruct funcEntries <-
                        decodeFuncEntry #pc #inst (#regRead @% "cs1") (#regRead @% "cs2")
                          (#regRead @% "scr") (#regRead @% "csr") #allMatches;
      
      RetE ((STRUCT { "pc" ::= #pc;
                      "inst" ::= #inst;
                      "badLower16?" ::= #uncompressOut @% "badLower16?";
                      "error?" ::= #uncompressOut @% "error?";
                      "fault?" ::= #uncompressOut @% "fault?";
                      "justFenceI?" ::= #uncompressOut @% "justFenceI?";
                      "bounds?" ::= #uncompressOut @% "bounds?";
                      "legal?" ::= #uncompressOut @% "legal?";
                      "decodes" ::= #decodes }) : DecodeOut @# ty) ).

  Definition ExecOut := STRUCT_TYPE {
                            "pc" :: Addr;
                            "notCompressed?" :: Bool;
                            "result" :: FuncOutput;
                            "cs1Idx" :: RegId;
                            "cdIdx" :: RegId;
                            "csrIdx" :: Bit (snd immField);
                            "justFenceI?" :: Bool
                          }.

  Definition getScrIdx (csrIdx: Bit (snd immField) @# ty) := UniBit (TruncLsb 5 _) csrIdx.
  
  Definition exec (decodeOut: DecodeOut @# ty) : ExecOut ## ty :=
    ( LETE funcOut : Maybe FuncOutput <- execFuncEntry (decodeOut @% "decodes");
      LETC funcOutData <- #funcOut @% "data";
      LETC pc <- decodeOut @% "pc" @% "val";
      LETC inst <- decodeOut @% "inst";
      LETC funcOutDataData <- #funcOutData @% "data";
      LETC exception <- !(decodeOut @% "bounds?")
                        || (decodeOut @% "error?")
                        || (decodeOut @% "fault?")
                        || !(decodeOut @% "legal?")
                        || !(#funcOut @% "valid")
                        || (#funcOutData @% "exception?");
      LETC exceptionCause : Data <-
                              ( IF !(decodeOut @% "bounds?")
                                then $CapBoundsViolation
                                else ( IF decodeOut @% "error?"
                                       then $InstAccessFault
                                       else ( IF decodeOut @% "fault?"
                                              then $InstPageFault
                                              else ( IF !(decodeOut @% "legal?") || !(#funcOut @% "valid")
                                                     then $InstIllegal
                                                     else #funcOutDataData @% "val" ))));
      LETC baseException <- ( IF !(decodeOut @% "bounds?")
                              then $$false
                              else ( IF (decodeOut @% "error?") || (decodeOut @% "fault?") ||
                                       !(decodeOut @% "legal?") || !(#funcOut @% "valid")
                                     then $$true
                                     else #funcOutData @% "baseException?" ) );
      LETC pcCapException <- ( IF !(decodeOut @% "bounds?")
                               then $$true
                               else #funcOutData @% "pcCapException?" );
      LETC exceptionValue <- ( IF decodeOut @% "error?" || decodeOut @% "fault?"
                               then #pc + ITE (decodeOut @% "badLower16?") $0 $2
                               else ( IF !(decodeOut @% "legal?") || !(#funcOut @% "valid")
                                      then ZeroExtendTruncLsb CapSz #inst
                                      else #funcOutDataData @% "cap" ) );
      LETC result : FuncOutput <- #funcOutData
                                    @%[ "exception?" <- #exception ]
                                    @%[ "baseException?" <- #baseException ]
                                    @%[ "pcCapException?" <- #pcCapException ]
                                    @%[ "data" <- ((STRUCT {
                                                        "tag" ::= #funcOutDataData @% "tag";
                                                        "cap" ::= #exceptionValue;
                                                        "val" ::= #exceptionCause }) : FullCapWithTag @# ty) ];
      RetE ((STRUCT { "pc" ::= #pc;
                      "notCompressed?" ::= isInstNotCompressed #inst;
                      "result" ::= #result;
                      "cs1Idx" ::= rs1 #inst;
                      "cdIdx" ::= rd #inst;
                      "csrIdx" ::= imm #inst;
                      "justFenceI?" ::= decodeOut @% "justFenceI?"} : ExecOut @# ty)) ).

  Definition memRetProcess (funcOut: FuncOutput @# ty) (memInfo: MemOpInfo @# ty) (memRet: DataRet @# ty) : FuncOutput ## ty :=
    ( LETC isStore <- memInfo @% "op" == $StOp;
      LETC memRetData <- memRet @% "data";
      LETC loadCap <- #memRetData @% "cap";
      LETC loadTag <- #memRetData @% "tag";
      LETE loadPerms <- getCapPerms capAccessors #loadCap;
      LETC loadIsSealed <- isSealed capAccessors #loadCap;
      LETC keepGL_LG <- !#loadTag || (memInfo @% "LG");
      LETC keepSD_LM <- !#loadTag || (memInfo @% "LM") || #loadIsSealed;
      LETC newLoadPerms <- #loadPerms
                             @%[ "GL" <- #keepGL_LG && (#loadPerms @% "GL") ]
                             @%[ "LG" <- #keepGL_LG && (#loadPerms @% "LG") ]
                             @%[ "SD" <- #keepSD_LM && (#loadPerms @% "SD") ]
                             @%[ "LM" <- #keepSD_LM && (#loadPerms @% "LM") ];
      LETC newLoadTag <- (memInfo @% "MC") && #loadTag;
      LETE newLoadCap <- setCapPerms capAccessors #newLoadPerms #loadCap;
      LETC exception <- (memRet @% "dataError?") || (memRet @% "dataFault?")
                        || (memRet @% "tagError?") || (memRet @% "tagFault?");
      LETC newDataVal : Data <- ( IF memRet @% "dataError?"
                                  then ITE #isStore $StoreAccessFault $LoadAccessFault
                                  else ( IF memRet @% "dataFault?"
                                         then ITE #isStore $StorePageFault $LoadPageFault
                                         else ( IF memRet @% "tagError?"
                                                then $TagAccessFault
                                                else ( IF memRet @% "tagFault?"
                                                       then $TagPageFault
                                                       else (#memRetData @% "val")))));
      LETC exceptionValue : Addr <- funcOut @% "addrOrScrOrCsrVal" +
                                      ZeroExtendTruncLsb Xlen
                                        (ITE ((memRet @% "dataError?") || (memRet @% "dataFault?"))
                                           (memRet @% "lowestByte")
                                           $0);
      (* TODO : Revocation *)
      LETC newFuncOutData <- STRUCT {
                                 "tag" ::= #newLoadTag;
                                 "cap" ::= ITE #exception #exceptionValue #newLoadCap;
                                 "val" ::= #newDataVal };
      RetE (funcOut @%[ "data" <- #newFuncOutData]
              @%[ "exception?" <- #exception ])).

  Definition memSpec (execOut: ExecOut @# ty) : ActionT ty ExecOut :=
    ( LET funcOut : FuncOutput <- execOut @% "result";
      LET memInfo <- unpack MemOpInfo (ZeroExtendTruncLsb (size MemOpInfo)
                                         (#funcOut @% "pcOrScrCapOrMemOp"));
      If !(#funcOut @% "exception?") && (#funcOut @% "mem?")
      then (
          LETA memRet : DataRet <- loadStoreReq (#memInfo @% "op" == $StOp) (#funcOut @% "addrOrScrOrCsrVal") (#memInfo @% "size")
                                     (#memInfo @% "cap?") (#funcOut @% "data") (#memInfo @% "sign?");
          convertLetExprSyntax_ActionT (memRetProcess #funcOut #memInfo #memRet) )
      else Ret #funcOut
      as retFuncOut;
      Ret (execOut @%[ "result" <- #retFuncOut ]) ).

  (* Exceptions must be handled before interrupts in case of a Store Access Error
     - it may have performed partial stores which should not be redone.
     But the spec says otherwise :(
   *)

  Local Notation "@^ x" := (procName ++ "_" ++ x)%string (at level 0).

  Definition wb (execOut: ExecOut @# ty) : ActionT ty Void :=
    ( LET result <- execOut @% "result";
      Read pcCap : Cap <- pcCapReg;
      Read pcVal : Addr <- pcValReg;
      Read prevPcCap: Cap <- prevPcCapReg;
      Read prevPcVal: Addr <- prevPcValReg;
      Read prevTaken: Bool <- prevTakenReg;
      Read reqJustFenceI: Bool <- reqJustFenceIReg;
      Read mtcc : FullCapWithTag <- @^"MTCC";
      Read mstatus: Data <- @^"mstatus";

      LET nextPcVal <- (IF #result @% "exception?"
                        then #mtcc @% "val"
                        else (IF #result @% "taken?"
                              then #result @% "addrOrScrOrCsrVal"
                              else #pcVal + (ITE (execOut @% "notCompressed?") $4 $2)));

      LET nextPcCap <- (IF #result @% "exception?"
                        then #mtcc @% "cap"
                        else (IF #result @% "changePcCap?"
                              then #result @% "pcOrScrCapOrMemOp"
                              else #prevPcCap));

      LET mstatusArr : Array Xlen Bool <-
                         BuildArray (fun i => match i with
                                              | Fin.FS _ (Fin.FS _ (Fin.FS _ (Fin.F1 _))) => #result @% "newIe"
                                              | _ => Const ty false
                                              end );

      LET csrIdx <- execOut @% "csrIdx";
      LET data <- #result @% "data";

      If !#reqJustFenceI || execOut @% "justFenceI?"
      then
        ( Write pcCapReg : Cap <- #nextPcCap;
          Write pcValReg : Addr <- #nextPcVal;
          Write prevPcCapReg : Cap <- #pcCap;
          Write prevPcValReg : Addr <- #pcVal;
          Write prevTakenReg : Bool <- !(#result @% "exception?") && (#result @% "taken?");
          Write reqJustFenceIReg : Bool <- !(#result @% "exception?") && (#result @% "fenceI?");
          If !(#result @% "exception?") && (#result @% "changeIe?")
          then ( Write @^"MStatus" : Data <- castBits (@Nat.mul_1_r Xlen) (pack #mstatusArr);
                 Retv )
          else Retv;
          If !(#result @% "exception?") && (#result @% "wb?") && isNotZero (execOut @% "cdIdx")
          then callWriteRegFile regsWrite (execOut @% "cdIdx") #data
          else Retv;
          If !(#result @% "exception?") && (#result @%"wbScr?")
          then writeRegs procName scrRegInfos (UniBit (TruncLsb 5 _) #csrIdx)
                 (STRUCT { "tag" ::= #result @% "scrTag";
                           "cap" ::= #result @% "pcOrScrCapOrMemOp";
                           "val" ::= #result @% "addrOrScrOrCsrVal" } : FullCapWithTag @# ty)
          else Retv;
          If !(#result @% "exception?") && (#result @%"wbCsr?")
          then writeRegs procName csrRegInfos #csrIdx (#result @% "addrOrScrOrCsrVal")
          else Retv;
          If #result @% "exception?"
          then ( Write @^"MEPCC" : FullCapWithTag <- STRUCT { "tag" ::= Const ty true;
                                                              "cap" ::= ITE #prevTaken #prevPcCap #pcCap;
                                                              "val" ::= ITE #prevTaken #prevPcVal #pcVal };
                 Write @^"MCause" : Data <- ITE (#result @% "baseException?") (#data @% "val") $CapException;
                 Write @^"MTval" :
                   Data <- (IF (#result @% "baseException?")
                            then #data @% "cap"
                            else ZeroExtendTruncLsb Xlen
                                   (pack (STRUCT { "S" ::= (#result @% "scrException?");
                                                   "capIdx" ::= (IF (#result @% "pcCapException?")
                                                                 then $0
                                                                 else ZeroExtendTruncLsb 5 (execOut @% "cs1Idx"));
                                                   "cause" ::= ZeroExtendTruncLsb 5 (#data @% "cap") } )));
                 Retv )
          else Retv;
          Retv )
      else Retv;
      Retv ).

  Definition runSpec : ActionT ty Void :=
    ( LETA fetchOut <- fetchSpec;
      LETAE uncompressOut <- uncompress #fetchOut;
      LETAE regReadIdOut <- regReadId #uncompressOut;
      LETA regReadOut <- regReadSpec #regReadIdOut;
      LETAE decodeOut <- decode #regReadOut;
      LETAE execOut <- exec #decodeOut;
      LETA memOut <- memSpec #execOut;
      wb #memOut ).
End Run.
