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

  (* TODO: Fix rules to make them disjoint; example setPcException is always called even if there's no exception in specInstBoundsException and specInstIllegalException. TODO *)
  Definition setTrapException (pred isCap isScr: Bool @# ty) (idx: Bit RegFixedIdSz @# ty)
    (cause value: Data @# ty):
    ActionT ty Void :=
    ( Read pcCap : Cap <- @^pcCapReg;
      Read pcVal : Addr <- @^pcValReg;
      WriteIf pred Then @^mepccReg : FullCapWithTag <- STRUCT { "tag" ::= $$true;
                                                                "cap" ::= #pcCap;
                                                                "val" ::= #pcVal };
      WriteIf pred Then @^mCauseReg : Data <- ITE isCap $CapException cause;
      WriteIf pred Then @^mtValReg : Data <-
                                       ITE isCap
                                         (ZeroExtendTruncLsb Xlen
                                            (pack (STRUCT { "S" ::= isScr;
                                                            "capIdx" ::= idx;
                                                            "cause" ::= ZeroExtendTruncLsb RegFixedIdSz cause })))
                                         value;
      Retv ).

  Definition setException (pred isCap isScr: Bool @# ty) (idx: Bit RegFixedIdSz @# ty)
    (cause value: Data @# ty) :=
    if hasTrap
    then setTrapException pred isCap isScr idx cause value
    else Retv.

  Definition gotoMtcc (pred: Bool @# ty) :=
    if hasTrap
    then (
        Read mtcc : FullCapWithTag <- @^mtccReg;
        WriteIf pred Then @^pcCapReg : Cap <- #mtcc @% "cap";
        WriteIf pred Then @^pcValReg : Addr <- #mtcc @% "val";
        Retv )
    else Retv.
  
  Definition specInstBoundsException :=
    ( Read pcCap : Cap <- @^pcCapReg;
      Read pcVal : Addr <- @^pcValReg;
      LETAE baseTop <- getCapBaseTop (STRUCT { "cap" ::= #pcCap; "val" ::= #pcVal });
      LET topBound <- ZeroExtend 1 #pcVal + $4 <= (#baseTop @% "top");
      LETA _ <- gotoMtcc (!#topBound);
      setException (!#topBound) ($$true) ($$false) $0 ($CapBoundsViolation) $0).

  Definition specInstIllegalException (ies: list (InstEntry FullOutput)) :=
    ( Read pcCap : Cap <- @^pcCapReg;
      Read pcVal : Addr <- @^pcValReg;
      LETAE baseTop <- getCapBaseTop (STRUCT { "cap" ::= #pcCap; "val" ::= #pcVal });
      LET topBound <- ZeroExtend 1 #pcVal + $4 <= (#baseTop @% "top");
      Read memArr : Array (NumMemBytes * NumBanks) (Bit 8) <- memArray;
      LET inst <- pack (readArrayConstSize #pcVal #memArr (InstSz/8));
      Read regs : Array NumRegs FullCapWithTag <- regsArray;
      LET illegal <- CABool And (map (fun ie => !(matchUniqId #inst (uniqId ie))) ies);
      LETA _ <- gotoMtcc (#topBound && #illegal);
      setException (#topBound && #illegal) $$false $$false
        $0 $InstIllegal (ZeroExtendTruncLsb Xlen #inst)).
  
  Definition specDecExecRule (ie: InstEntry FullOutput) :=
    ( Read pcCap : Cap <- @^pcCapReg;
      Read pcVal : Addr <- @^pcValReg;
      LETAE baseTop <- getCapBaseTop (STRUCT { "cap" ::= #pcCap; "val" ::= #pcVal });
      LET topBound <- ZeroExtend 1 #pcVal + $4 <= (#baseTop @% "top");
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

      LET matchNoException <- #topBound && #instMatch && !(#out @% "exception?");

      WriteIf #matchNoException Then
        regsArray: Array NumRegs FullCapWithTag <- #updRegs;
      LETA _ <- storeReqSpec procName (#matchNoException && (#out @% "mem?") && (#out @% "store?")) (#out @% "pcMemAddr")
                  (#out @% "memSize") (#out @% "memCap?")
                  (STRUCT { "tag" ::= #out @% "cdTag";
                            "cap" ::= #out @% "cdCap";
                            "val" ::= #out @% "cdVal" });

      Read mtcc : FullCapWithTag <- @^mtccReg;
      WriteIf (#topBound && #instMatch) Then
        @^pcCapReg : Cap <- (IF (#out @% "exception?")
                             then #mtcc @% "cap"
                             else ITE (#out @% "changePcCap?") (#out @% "pcCap") #pcCap);
      WriteIf (#topBound && #instMatch) Then
        @^pcValReg : Addr <- (IF (#out @% "exception?")
                              then #mtcc @% "val"
                              else ITE (#out @% "taken?") (#out @% "pcMemAddr") (#pcVal + $(InstSz/8)));

      LET matchException <- #topBound && #instMatch && (#out @% "exception?");

      setException #matchException (!(#out @% "baseException?")) (#out @% "scrException?")
        (ITE (#out @% "pcCapException?") $0 (ZeroExtendTruncLsb RegFixedIdSz #cs1Idx))
        (#out @% "exceptionCause") (#out @% "exceptionValue")
      ).
End Run.
