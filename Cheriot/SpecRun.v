Require Import Kami.AllNotations.
Require Import ProcKami.Cheriot.Lib ProcKami.Cheriot.Types.
Require Import ProcKami.Cheriot.DecExec ProcKami.Cheriot.MemSpec.

Section Run.
  Context `{procParams: ProcParams}.
  
  Variable ty: Kind -> Type.

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Variable scrs: list ScrReg.
  Variable csrs: list CsrReg.

  Let scrRegInfos := map scrRegInfo scrs.
  Let csrRegInfos := map csrRegInfo csrs.

  Local Notation "@^ x" := (procName ++ "_" ++ x)%string (at level 0).

  Definition setTrapException (pred isCap isScr: Bool @# ty) (idx: Bit RegFixedIdSz @# ty) (cause value: Data @# ty):
    ActionT ty Void :=
    ( Read pcCap : Cap <- pcCapReg;
      Read pcVal : Addr <- pcValReg;
      Read prevPcCap : Cap <- prevPcCapReg;
      Read prevPcVal : Addr <- prevPcValReg;
      WriteIf pred Then @^"MEPCC" : FullCapWithTag <- STRUCT { "tag" ::= Const ty true;
                                                               "cap" ::= #pcCap;
                                                               "val" ::= #pcVal };
      WriteIf pred Then @^"MEPrevPCC" : FullCapWithTag <- STRUCT { "tag" ::= Const ty true;
                                                                   "cap" ::= #prevPcCap;
                                                                   "val" ::= #prevPcVal };
      WriteIf pred Then @^"MCause" : Data <- ITE isCap $CapException cause;
      WriteIf pred Then @^"MTVal" : Data <-
                                      ITE isCap
                                        (ZeroExtendTruncLsb Xlen
                                           (pack (STRUCT { "S" ::= isScr;
                                                           "capIdx" ::= idx;
                                                           "cause" ::= ZeroExtendTruncLsb RegFixedIdSz cause })))
                                        value;
      Retv ).

  Definition setException (pred isCap isScr: Bool @# ty) (idx: Bit RegFixedIdSz @# ty) (cause value: Data @# ty) :=
    if hasTrap
    then setTrapException pred isCap isScr idx cause value
    else Retv.

  Definition setPcException :=
    if hasTrap
    then (
        Read mtcc : FullCapWithTag <- @^"MTCC";
        Write pcCapReg : (@Cap procParams) <- #mtcc @% "cap";
        Write pcValReg : Addr <- #mtcc @% "val";
        Retv )
    else Retv.
  
  Definition specInstBoundsException :=
    ( Read pcCap : Cap <- pcCapReg;
      Read pcVal : Addr <- pcValReg;
      Read prevPcCap : Cap <- prevPcCapReg;
      Read prevPcVal : Addr <- prevPcValReg;
      LETAE baseTop <- getCapBaseTop capAccessors #pcCap #pcVal;
      LET baseBound <- #pcVal >= (#baseTop @% "base");
      LET topBound <- ZeroExtend 1 #pcVal + $4 <= (#baseTop @% "top");
      LET instBounds <- #baseBound && #topBound;
      LETA _ <- setPcException;
      setException (!#instBounds) ($$true) ($$false) $0 ($CapBoundsViolation) $0).

  Definition specInstIllegalException (ies: list (InstEntry FullOutput)) :=
    ( Read pcCap : Cap <- pcCapReg;
      Read pcVal : Addr <- pcValReg;
      LETAE baseTop <- getCapBaseTop capAccessors #pcCap #pcVal;
      LET baseBound <- #pcVal >= (#baseTop @% "base");
      LET topBound <- ZeroExtend 1 #pcVal + $4 <= (#baseTop @% "top");
      LET instBounds <- #baseBound && #topBound;
      Read memArr : Array (NumMemBytes * NumBanks) (Bit 8) <- memArray;
      LET inst <- pack (readArrayConstSize #pcVal #memArr (InstSz/8));
      Read regs : Array NumRegs FullCapWithTag <- regsArray;
      LET illegal <- CABool And (map (fun ie => !(matchUniqId #inst (uniqId ie))) ies);
      LETA _ <- setPcException;
      setException (#instBounds && #illegal) $$false $$false $0 $InstIllegal (ZeroExtendTruncLsb Xlen #inst)).
  
  Definition specDecExecRule (ie: InstEntry FullOutput) :=
    ( Read pcCap : Cap <- pcCapReg;
      Read pcVal : Addr <- pcValReg;
      LETAE baseTop <- getCapBaseTop capAccessors #pcCap #pcVal;
      LET baseBound <- #pcVal >= (#baseTop @% "base");
      LET topBound <- ZeroExtend 1 #pcVal + $4 <= (#baseTop @% "top");
      LET instBounds <- #baseBound && #topBound;
      Read memArr : Array (NumMemBytes * NumBanks) (Bit 8) <- memArray;
      LET inst <- pack (readArrayConstSize #pcVal #memArr (InstSz/8));
      Read regs : Array NumRegs FullCapWithTag <- regsArray;
      let instProps := instProperties ie in
      LET cs1Idx <- if (Nat.eq_dec (implicitReg instProps) 0) then (rs1 #inst) else $(implicitReg instProps);
      LET cs2Idx <- rs2 #inst;
      LET scrIdx <- if (Nat.eq_dec (implicitScr instProps) 0)
                    then (rs2Fixed #inst) else $(implicitScr instProps);
      LET csrIdx <- if (weq (implicitCsr instProps) (wzero _)) then (imm #inst) else $$(implicitCsr instProps);
      LET cs1 <- #regs@[#cs1Idx];
      LET cs2 <- #regs@[#cs2Idx];
      LETA scr <- readRegs procName scrRegInfos #scrIdx;
      LETA csr <- readRegs procName csrRegInfos #csrIdx;
      LETAE out <- spec ie (STRUCT { "cap" ::= #pcCap; "val" ::= #pcVal }) #inst #cs1 #cs2 #scr #csr;
      LETA ld <- loadReqSpec (#out @% "pcMemAddr") (#out @% "memSize") (#out @% "memCap?")
                   (#out @% "ldSigned?");
      LET cd <- ITE (#out @% "mem?" && !(#out @% "store?")) #ld (STRUCT { "tag" ::= #out @% "cdTag";
                                                                          "cap" ::= #out @% "cdCap";
                                                                          "val" ::= #out @% "cdVal"});
      LET cdIdx <- rd #inst;
      LET instMatch <- matchUniqId #inst (uniqId ie);
      LET updRegs <- #regs @[ #cdIdx <- ITE ((#cdIdx != $0) && (#out @% "wb?")) #cd (#regs@[#cdIdx])];

      Read prevPcCap : Cap <- prevPcCapReg;
      Read prevPcVal : Addr <- prevPcValReg;

      LET matchNoException <- #instBounds && #instMatch && !(#out @% "exception?");

      WriteIf #matchNoException Then
        regsArray: Array NumRegs FullCapWithTag <- #updRegs;
      WriteIf #matchNoException Then
        prevPcCapReg : Cap <- #pcCap;
      WriteIf #matchNoException Then
        prevPcValReg : Addr <- #pcVal;
      LETA _ <- storeReqSpec (#matchNoException && (#out @% "mem?") && (#out @% "store?")) (#out @% "pcMemAddr")
                  (#out @% "memSize") (#out @% "memCap?") #cd;

      Read mtcc : FullCapWithTag <- @^"MTCC";
      WriteIf (#instBounds && #instMatch) Then
        pcCapReg : Cap <- (IF (#out @% "exception?")
                           then #mtcc @% "cap"
                           else ITE (#out @% "changePcCap?") (#out @% "pcCap") #pcCap);
      WriteIf (#instBounds && #instMatch) Then
        pcValReg : Addr <- (IF (#out @% "exception?")
                            then #mtcc @% "val"
                            else ITE (#out @% "taken?") (#out @% "pcMemAddr") (#pcVal + $(InstSz/8)));

      LET matchException <- #instBounds && #instMatch && (#out @% "exception?");

      setException #matchException (!(#out @% "baseException?")) (#out @% "scrException?")
        (ITE (#out @% "pcCapException?") $0 (ZeroExtendTruncLsb RegFixedIdSz #cs1Idx))
        (#out @% "exceptionCause") (#out @% "exceptionValue")).
End Run.
