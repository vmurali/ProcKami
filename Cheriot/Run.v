Require Import Kami.AllNotations.
Require Import ProcKami.Cheriot.Lib ProcKami.Cheriot.Types.
Require Import ProcKami.Cheriot.DecExec ProcKami.Cheriot.BankedMem.

Section Run.
  Context `{procParams: ProcParams}.
  Variable ty: Kind -> Type.

  Definition CompressedOutput :=
    STRUCT_TYPE {
        "data"              :: FullCapWithTag;
        "pcOrScrCapOrMemOp" :: Cap;
        "addrOrScrOrCsrVal" :: Addr;
        "wb?"               :: Bool;
        "taken?"            :: Bool;
        "changePcCap?"      :: Bool;
        "mem?"              :: Bool;
        "exception?"        :: Bool;
        "baseException?"    :: Bool; (* non-cap exception *)
        "pcCapException?"   :: Bool; (* cap exception caused by PC *)
        "fenceI?"           :: Bool;
        "changeIe?"         :: Bool;
        "newIe"             :: Bool;
        "wbScr?"            :: Bool;
        "scrTag"            :: Bool;
        "scrException?"     :: Bool;
        "wbCsr?"            :: Bool}.

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Definition compressOutput (inp: FullOutput @# ty): CompressedOutput ## ty :=
    ( LETC memOp : MemOpInfo <-
                     STRUCT {
                         "op" ::= ITE (inp @% "store?") $StOp $LdOp;
                         "size" ::= inp @% "memSize";
                         "MC" ::= inp @% "ldPerms" @% "MC";
                         "LM" ::= inp @% "ldPerms" @% "LM";
                         "LG" ::= inp @% "ldPerms" @% "LG";
                         "sign?" ::= inp @% "ldSigned?";
                         "cap?" ::= inp @% "memCap?" };
      LETC cd : FullCapWithTag <-
                  STRUCT {
                      "tag" ::= inp @% "cdTag";
                      "cap" ::= ITE (inp @% "exception?") (inp @% "exceptionValue") (inp @% "cdCap");
                      "val" ::= (IF (inp @% "exception?")
                                 then inp @% "exceptionCause"
                                 else inp @% "cdVal") };
      RetE (STRUCT {
                "data" ::= #cd;
                "pcOrScrCapOrMemOp" ::= (IF (inp @% "mem?")
                                         then ZeroExtendTruncLsb CapSz (pack #memOp)
                                         else (IF (inp @% "wbScr?")
                                               then inp @% "scrCap"
                                               else inp @% "pcCap"));
                "addrOrScrOrCsrVal" ::= (IF (inp @% "wbScr?")
                                         then inp @% "scrVal"
                                         else (IF (inp @% "wbCsr?")
                                               then inp @% "csrVal"
                                               else inp @% "pcMemAddr"));
                "wb?" ::= inp @% "wb?";
                "taken?" ::= inp @% "taken?";
                "changePcCap?" ::= inp @% "changePcCap?";
                "mem?" ::= inp @% "mem?";
                "exception?" ::= inp @% "exception?";
                "baseException?" ::= inp @% "baseException?";
                "pcCapException?" ::= inp @% "pcCapException?";
                "fenceI?" ::= inp @% "fenceI?";
                "changeIe?" ::= inp @% "changeIe?";
                "newIe" ::= inp @% "newIe";
                "wbScr?" ::= inp @% "wbScr?";
                "scrTag" ::= inp @% "scrTag";
                "scrException?" ::= inp @% "scrException?";
                "wbCsr?" ::= inp @% "wbCsr?" } : CompressedOutput @# ty) ).

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
      RetAE (instRetProcess #pcCap #pcVal #instRet) ).

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
      LETC implicitRegVal  <- implicitRegPropFn #allMatches;
      LETC implicitRegProp <- isNotZero #implicitRegVal;
      LETC implicitScrVal  <- implicitScrPropFn #allMatches;
      LETC implicitScrProp <- isNotZero #implicitScrVal;
      LETC implicitCsrVal  <- implicitCsrPropFn #allMatches;
      LETC implicitCsrProp <- isNotZero #implicitCsrVal;

      RetE (STRUCT { "uncompressOut" ::= uncompressOut;
                     "allMatches" ::= #allMatches;
                     "regReadId" ::=
                       (STRUCT { "cs1?" ::= (#hasCs1Prop || #implicitRegProp);
                                 "cs1Idx" ::= ITE #implicitRegProp #implicitRegVal (rs1 #inst);
                                 "cs2?" ::= #hasCs2Prop;
                                 "cs2Idx" ::= rs2 #inst;
                                 "scr?" ::= (#hasScrProp || #implicitScrProp);
                                 "scrIdx" ::= ITE #implicitScrProp #implicitScrVal (rs2Fixed #inst);
                                 "csr?" ::= (#hasCsrProp || #implicitCsrProp);
                                 "csrIdx" ::= ITE #implicitCsrProp #implicitCsrVal (imm #inst) }
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
                            "inst" :: Inst;
                            "result" :: CompressedOutput;
                            "justFenceI?" :: Bool }.

  Definition getScrIdx (csrIdx: Bit (snd immField) @# ty) := UniBit (TruncLsb 5 _) csrIdx.
  
  Definition exec (decodeOut: DecodeOut @# ty) : ExecOut ## ty :=
    ( LETE funcOut : Maybe FullOutput <- execFuncEntry (decodeOut @% "decodes");
      LETE funcOutData <- compressOutput (#funcOut @% "data");
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
      LETC result : CompressedOutput <- #funcOutData
                                    @%[ "exception?" <- #exception ]
                                    @%[ "baseException?" <- #baseException ]
                                    @%[ "pcCapException?" <- #pcCapException ]
                                    @%[ "data" <- ((STRUCT {
                                                        "tag" ::= #funcOutDataData @% "tag";
                                                        "cap" ::= #exceptionValue;
                                                        "val" ::= #exceptionCause }) : FullCapWithTag @# ty) ];
      RetE ((STRUCT { "inst" ::= #inst;
                      "result" ::= #result;
                      "justFenceI?" ::= decodeOut @% "justFenceI?" } : ExecOut @# ty)) ).

  Definition memRetProcess (funcOut: CompressedOutput @# ty) (memInfo: MemOpInfo @# ty) (memRet: DataRet @# ty) : CompressedOutput ## ty :=
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

  Definition MemOutData := STRUCT_TYPE { "inst" :: Inst;
                                         "result" :: CompressedOutput }.

  Definition memSpec (execOut: ExecOut @# ty) : ActionT ty (Maybe MemOutData) :=
    ( LET funcOut : CompressedOutput <- execOut @% "result";
      LET memInfo <- unpack MemOpInfo (ZeroExtendTruncLsb (size MemOpInfo)
                                         (#funcOut @% "pcOrScrCapOrMemOp"));
      Read reqJustFenceI: Bool <- reqJustFenceIReg;
      LET exception <- #funcOut @% "exception?";
      LET dontDrop <- !#reqJustFenceI || execOut @% "justFenceI?";

      If #dontDrop && !#exception && (#funcOut @% "mem?")
      then (
          LETA memRet : DataRet <- loadStoreReq (#memInfo @% "op" == $StOp) (#funcOut @% "addrOrScrOrCsrVal")
                                     (#memInfo @% "size") (#memInfo @% "cap?") (#funcOut @% "data") (#memInfo @% "sign?");
          RetAE (memRetProcess #funcOut #memInfo #memRet) )
      else Ret #funcOut
      as retFuncOut ;
      LET setFenceI <- !#exception && (#funcOut @% "fenceI?");
      WriteIf #dontDrop Then reqJustFenceIReg : Bool <- #setFenceI;
      LET memOutData : MemOutData <- STRUCT { "inst" ::= execOut @% "inst";
                                              "result" ::= #retFuncOut };
      Ret (STRUCT {"valid" ::= #dontDrop ; "data" ::= #memOutData } : Maybe _ @# _) ).

  (* Exceptions must be handled before interrupts in case of a Store Access Error
     - it may have performed partial stores which should not be redone.
     But the spec says otherwise :(
   *)

  Local Notation "@^ x" := (procName ++ "_" ++ x)%string (at level 0).

  Definition wb (spec : bool) (memOut: Maybe MemOutData @# ty) : ActionT ty Void :=
    ( If (memOut @% "valid")
      then (
          LET memOutData <- memOut @% "data";
          LET result <- #memOutData @% "result";
          LET exception <- #result @% "exception?";
          Read pcCap : Cap <- pcCapReg;
          Read pcVal : Addr <- pcValReg;
          Read prevPcCap: Cap <- prevPcCapReg;
          Read prevPcVal: Addr <- prevPcValReg;
          Read mtcc : FullCapWithTag <- @^"MTCC";
          Read mstatus: Data <- @^"mstatus";

          LET inst <- #memOutData @% "inst";
          LET notCompressed <- isInstNotCompressed #inst;

          LET nextPcVal <- (IF #exception
                            then (if spec then #pcVal else (#mtcc @% "val"))
                            else (IF #result @% "taken?"
                                  then #result @% "addrOrScrOrCsrVal"
                                  else #pcVal + (ITE #notCompressed $4 $2)));

          LET nextPcCap <- (IF #exception
                            then (if spec then #pcCap else (#mtcc @% "cap"))
                            else (IF #result @% "changePcCap?"
                                  then #result @% "pcOrScrCapOrMemOp"
                                  else #prevPcCap));

          LET mstatusArr : Array Xlen Bool <-
                             BuildArray (fun i => match i with
                                                  | Fin.FS _ (Fin.FS _ (Fin.FS _ (Fin.F1 _))) => #result @% "newIe"
                                                  | _ => Const ty false
                                                  end );

          LET csrIdx <- imm #inst;
          LET cdIdx <- rd #inst;
          LET cs1Idx <- rs1 #inst;
          LET cs2Idx <- rs2Fixed #inst;
          LET data <- #result @% "data";
          LET setFenceI <- !#exception && (#result @% "fenceI?");

          Write pcCapReg : Cap <- #nextPcCap;
          Write pcValReg : Addr <- #nextPcVal;
          Write prevPcCapReg : Cap <- #pcCap;
          Write prevPcValReg : Addr <- #pcVal;
          WriteIf #setFenceI Then startFenceIReg : Bool <- $$true;

          WriteIf (!#exception && (#result @% "changeIe?")) Then
            @^"MStatus" : Data <- castBits (@Nat.mul_1_r Xlen) (pack #mstatusArr);

          LETA _ <- writeRegsPred procName scrRegInfos (!#exception && (#result @% "wbScr?"))
                      #cs2Idx (STRUCT { "tag" ::= #result @% "scrTag";
                                        "cap" ::= #result @% "pcOrScrCapOrMemOp";
                                        "val" ::= #result @% "addrOrScrOrCsrVal" } : FullCapWithTag @# ty);

          LETA _ <- writeRegsPred procName csrRegInfos (!#exception && (#result @% "wbCsr?"))
                      #csrIdx (#result @% "addrOrScrOrCsrVal");

          WriteIf (#exception) Then
            @^"MEPCC" : FullCapWithTag <- STRUCT { "tag" ::= Const ty true;
                                                   "cap" ::= #pcCap;
                                                   "val" ::= #pcVal };

          WriteIf (#exception) Then
            @^"MEPrevPCC" : FullCapWithTag <- STRUCT { "tag" ::= #result @% "taken?";
                                                       "cap" ::= #prevPcCap;
                                                       "val" ::= #prevPcVal };

          WriteIf (#exception) Then
            @^"MCause" : Data <- ITE (#result @% "baseException?") (#data @% "val") $CapException;

          WriteIf (#exception) Then
            @^"MTVal" : Data <- (IF (#result @% "baseException?")
                                 then #data @% "cap"
                                 else ZeroExtendTruncLsb Xlen
                                        (pack (STRUCT { "S" ::= (#result @% "scrException?");
                                                        "capIdx" ::= (IF (#result @% "pcCapException?")
                                                                      then $0
                                                                      else ZeroExtendTruncLsb 5 #cs1Idx);
                                                        "cause" ::= ZeroExtendTruncLsb 5 (#data @% "val") } )));

          If !#exception && (#result @% "wb?") && isNotZero #cdIdx
          then callWriteRegFile regsWrite #cdIdx #data
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
      wb true #memOut ).
End Run.
