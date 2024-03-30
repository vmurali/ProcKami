Require Import Kami.AllNotations.
Require Import ProcKami.Cheriot.Lib ProcKami.Cheriot.Types.
Require Import ProcKami.Cheriot.DecExec ProcKami.Cheriot.MemSpec.

Section Run.
  Context `{coreConfigParams: CoreConfigParams}.
  Instance memParamsInstance: MemParams := memParams.

  Variable ty: Kind -> Type.

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Variable scrs: list ScrReg.
  Variable csrs: list CsrReg.

  Let scrRegInfos := map scrRegInfo scrs.
  Let csrRegInfos := map csrRegInfo csrs.

  Local Notation "@^ x" := (procName ++ "_" ++ x)%string (at level 0).

  Definition handleException
    (pred isException baseException scrException pcCapException wbScr wbCsr changePcVal changePcCap: Bool @# ty)
    (newPcVal: Addr @# ty) (newPcCap: Cap @# ty) (newScr: FullCapWithTag @# ty) (newCsr: Data @# ty)
    (scrIdx: ScrId @# ty) (csrIdx: Bit CsrIdSz @# ty) (exceptionCause exceptionVal: Data @# ty)
    (exceptionIdx: Bit RegFixedIdSz @# ty) : ActionT ty Void :=
    ( Read pcVal : Addr <- @^pcValReg;
      Read pcCap : Cap <- @^pcCapReg;
      LET pcc : FullCapWithTag <- STRUCT { "tag" ::= $$true;
                                           "cap" ::= #pcCap;
                                           "val" ::= #pcVal };
      LETA exceptionPc <- if hasTrap
                          then
                            ( Read mtcc : FullCapWithTag <- @^mtccReg;
                              Ret #mtcc )
                          else Ret #pcc ;

      WriteIf pred Then
        @^pcValReg : Addr <- (IF isException
                              then #exceptionPc @% "val"
                              else ITE changePcVal newPcVal #pcVal);
      WriteIf pred Then
        @^pcCapReg : Cap <- (IF isException
                             then #exceptionPc @% "cap"
                             else ITE changePcCap newPcCap #pcCap);

      if hasTrap
      then
        ( Read mepccVal : FullCapWithTag <- @^mepccReg;
          WriteIf pred Then
            @^mepccReg : FullCapWithTag <- (IF isException
                                            then #pcc
                                            else (IF scrIdx == $$(getRegScrId mepcc)
                                                  then newScr
                                                  else #mepccVal));

          Read mStatusVal : Data <- @^mStatusReg;
          LET mStatusArr <- unpack (Array Xlen Bool) #mStatusVal;
          LET newMStatusVal <- pack (UpdateArrayConst (UpdateArrayConst #mStatusArr (@natToFin 3 _) ($$false))
                                       (@natToFin 7 _) (#mStatusArr ![3]));
          WriteIf pred Then
            @^mStatusReg : Data <- (IF isException
                                    then #newMStatusVal
                                    else (IF csrIdx == $$(getCsrId mstatus)
                                          then newCsr
                                          else #mStatusVal));

          Read mCauseVal : Data <- @^mCauseReg;
          WriteIf pred Then
            @^mCauseReg : Data <- (IF isException
                                   then ITE baseException exceptionCause $CapException
                                   else (IF wbScr && csrIdx == $$(getCsrId mcause)
                                         then newCsr
                                         else #mCauseVal));
          
          Read mtValVal : Data <- @^mtValReg;
          WriteIf pred Then
            @^mtValReg : Data <- (IF isException
                                  then ITE baseException
                                         exceptionVal
                                         (ZeroExtendTo Xlen
                                            (pack (STRUCT { "S" ::= scrException;
                                                            "capIdx" ::= exceptionIdx;
                                                            "cause" ::= TruncLsbTo RegFixedIdSz _
                                                                          exceptionCause })))
                                  else (IF wbCsr && csrIdx == $$(getCsrId mtval)
                                        then newCsr
                                        else #mtValVal));
          
          
          LETA _ <- writeRegsPred procName scrRegInfos
                      (pred && !isException && wbScr && (scrIdx != $$(getRegScrId mepcc)))
                      scrIdx newScr;

          LETA _ <- writeRegsPred procName csrRegInfos
                      (pred && !isException && wbCsr &&
                         (csrIdx != $$(getCsrId mstatus)) &&
                         (csrIdx != $$(getCsrId mcause)) &&
                         (csrIdx != $$(getCsrId mtval)))
                      csrIdx newCsr;

          Retv
        )
      else Retv).

  Definition specTimerIncAndInterruptSetRule :=
    ( if hasTrap
      then
      ( Read mTime : Data <- @^mTimeReg;
        Read mTimeCmp: Data <- @^mTimeCmpReg;
        LET msb <- UniBit (TruncMsb (Xlen - 1) 1) (#mTime - #mTimeCmp);
        WriteIf (isZero #msb) Then @^mtiReg : Bool <- $$true;
        Write @^mTimeReg : Data <- #mTime + $1;
        Retv )
      else Retv ).

  Definition specTimerInterruptTakeRule :=
    ( if hasTrap
      then
        ( Read mti : Bool <- @^mtiReg;
          Write @^mtiReg : Bool <- $$false;
          handleException ($$true) #mti ($$true) ($$false) ($$false) ($$false) ($$false) ($$false) ($$false)
            ($0) ($$(getDefaultConst Cap)) ($$(getDefaultConst FullCapWithTag)) ($0)
            ($0) ($0) ({<$$WO~1, $$(natToWord (Xlen-1) TimerInterrupt)>}) ($0)
            ($0) )
      else Retv ).
  
  Definition specInstBoundsExceptionRule :=
    ( Read pcCap : Cap <- @^pcCapReg;
      Read pcVal : Addr <- @^pcValReg;
      LETAE baseTop <- getCapBaseTop (STRUCT { "cap" ::= #pcCap; "val" ::= #pcVal });
      LET topBound <- ZeroExtend 1 #pcVal + $(InstSz/8) <= (#baseTop @% "top");
      if hasTrap
      then
        ( Read mti : Bool <- @^mtiReg;
          handleException (!#mti) (!#topBound) ($$false) ($$false) ($$true) ($$false) ($$false) ($$false) ($$false)
            ($0) ($$(getDefaultConst Cap)) ($$(getDefaultConst FullCapWithTag)) ($0)
            ($0) ($0) ($CapBoundsViolation) ($0)
            ($0) )
      else Retv ).

  Definition specInstIllegalExceptionRule (ies: list InstEntrySpec) :=
    ( Read pcCap : Cap <- @^pcCapReg;
      Read pcVal : Addr <- @^pcValReg;
      LETAE baseTop <- getCapBaseTop (STRUCT { "cap" ::= #pcCap; "val" ::= #pcVal });
      LET topBound <- ZeroExtend 1 #pcVal + $(InstSz/8) <= (#baseTop @% "top");
      Read memArr : Array (NumMemBytes * NumBanks) (Bit 8) <- memArray;
      LET inst <- pack (readArrayConstSize #pcVal #memArr (InstSz/8));
      Read regs : Array NumRegs FullCapWithTag <- regsArray;
      LET illegal <- CABool And (map (fun ie => !(matchUniqId #inst (uniqId ie))) ies);
      if hasTrap
      then
        ( Read mti : Bool <- @^mtiReg;
          handleException (!#mti && #topBound) #illegal ($$true) ($$false) ($$true) ($$false) ($$false) ($$false) ($$false)
            ($0) ($$(getDefaultConst Cap)) ($$(getDefaultConst FullCapWithTag)) ($0)
            ($0) ($0) ($InstIllegal) (ZeroExtendTo Xlen #inst)
            ($0) )
      else Retv ).
  
  Definition specDecExecRule (ie: InstEntrySpec) :=
    ( Read pcCap : Cap <- @^pcCapReg;
      Read pcVal : Addr <- @^pcValReg;
      LETAE baseTop <- getCapBaseTop (STRUCT { "cap" ::= #pcCap; "val" ::= #pcVal });
      LET topBound <- ZeroExtend 1 #pcVal + $(InstSz/8) <= (#baseTop @% "top");
      Read memArr : Array (NumMemBytes * NumBanks) (Bit 8) <- memArray;
      LET inst <- pack (readArrayConstSize #pcVal #memArr (InstSz/8));
      Read regs : Array NumRegs FullCapWithTag <- regsArray;
      let instProps := instProperties ie in
      LET cs1Idx <- if (weq (implicitReg instProps) (wzero _)) then (rs1 #inst) else $$(implicitReg instProps);
      LET cs2Idx <- rs2Fixed #inst;
      LET scrIdx <- if (weq (implicitScr instProps) (wzero _))
                    then (rs2Fixed #inst) else $$(implicitScr instProps);
      LET csrIdx <- if (weq (implicitCsr instProps) (wzero _)) then (imm #inst) else $$(implicitCsr instProps);
      LET cs1 <- #regs@[#cs1Idx];
      LET cs2 <- #regs@[TruncLsbTo RegIdSz _ #cs2Idx];
      LETA scr <- readRegs procName scrRegInfos #scrIdx FullCapWithTag;
      LETA csr <- readRegs procName csrRegInfos #csrIdx Data;
      LETAE out <- spec ie (STRUCT { "cap" ::= #pcCap; "val" ::= #pcVal }) #inst #cs1 #cs2 #scr #csr;
      LETA ld <- loadReqSpec procName (#out @% "pcMemAddr") (#out @% "memSize") (#out @% "memCap?")
                   (#out @% "ldSigned?");
      LET cd <- ITE (#out @% "mem?" && !(#out @% "store?"))
                  (STRUCT { "tag" ::= #ld @% "tag";
                            "cap" ::= #ld @% "cap";
                            "val" ::= #ld @% "val" })
                  (STRUCT { "tag" ::= #out @% "cdTag";
                            "cap" ::= #out @% "cdCap";
                            "val" ::= #out @% "cdVal"});
      LET cdIdx <- rd #inst;
      LET instMatch <- matchUniqId #inst (uniqId ie);
      LET updRegs <- #regs @[ #cdIdx <- ITE ((#cdIdx != $0) && (#out @% "wb?")) #cd (#regs@[#cdIdx])];

      LETA mti <- if hasTrap
                  then ( Read mti : Bool <- @^mtiReg;
                         Ret #mti )
                  else Ret $$false;
      handleException (!#mti && #topBound && #instMatch) (#out @% "exception?") (#out @% "baseException?")
        (#out @% "scrException?") (#out @% "pcCapException?") (#out @% "wbScr?") (#out @% "wbCsr?")
        ($$true) (#out @% "changePcCap?")
        (ITE (#out @% "taken?") (#out @% "pcMemAddr") (#pcVal + $(InstSz/8))) (#out @% "pcCap")
        (STRUCT { "tag" ::= #out @% "scrTag";
                  "cap" ::= #out @% "scrCap";
                  "val" ::= #out @% "scrVal" }) (#out @% "csrVal")
        #cs2Idx #csrIdx (#out @% "exceptionCause") (#out @% "exceptionValue")
        (ITE (#out @% "pcCapException?") $0 (ZeroExtendTo RegFixedIdSz #cs1Idx)) ).
End Run.
