Require Import Kami.AllNotations.
Require Import ProcKami.Cheriot.Lib ProcKami.Cheriot.Types ProcKami.Cheriot.CoreConfig.

Section InBoundsTy.
  Variable ty: Kind -> Type.
  Variable x : Bit 32 @# ty.
  Variable inCap: Cap @# ty.
  Variable inVal: Bit 32 @# ty.

  Local Open Scope kami_expr.

  Let inRange := getCapBaseTop (STRUCT { "cap" ::= inCap; "val" ::= inVal }).

  Definition inBounds :=
    ( LETE inRangeVal <- inRange;
      RetE ((x >= #inRangeVal @% "base") && (ZeroExtend 1 x < #inRangeVal @% "top"))).

  Definition systemAccess :=
    ( LETC perms <- getCapPerms inCap;
      RetE (#perms @% "SR") ).
End InBoundsTy.

Section InBoundsInits.
  Variable x: word 32.
  Variable rfInit: Fin.t 32 -> type FullCapWithTag.
  Variable capPcInit: type Cap.
  Variable valPcInit: word 32.

  Local Open Scope kami_expr.

  Definition InBoundsRf :=
    exists i, evalLetExpr (inBounds (Const _ x)
                             (Var type (SyntaxKind _) (rfInit i) @% "cap")
                             (Var type (SyntaxKind _) (rfInit i) @% "val")) = true.
  Definition InBoundsPc :=
    evalLetExpr (inBounds (Const _ x) (Const _ (convTypeToConst capPcInit)) (Const _ valPcInit)) = true.

  Definition SystemAccessRf :=
    exists i, evalLetExpr (systemAccess (Var type (SyntaxKind _) (rfInit i) @% "cap")) = true.

  Definition SystemAccessPc :=
    evalLetExpr (systemAccess (Const _ (convTypeToConst capPcInit))) = true.
End InBoundsInits.

Section InBoundsCoreConfig.
  Variable x: word 32.
  Variable p: CoreConfigParams.
  Definition InBoundsInit := InBoundsRf x (@regsInit p) \/ InBoundsPc x (@pcCapInit p)
                                                             (wcombine (@pcValInit p) (wzero 2)).
  Definition SystemAccessInit := SystemAccessRf (@regsInit p) \/ SystemAccessPc (@pcCapInit p).
End InBoundsCoreConfig.

Record SpecIsolation := {
    cores: list CoreConfigParams;
    disjointNamesCores: NoDup (map (@procName) cores);
    disjointBoundsCores: forall x p, In p cores -> InBoundsInit x p -> forall q,
                                         In q cores -> InBoundsInit x q -> @procName p <> @procName q -> False;
    noScrAccessCores: forall p, In p cores -> SystemAccessInit p -> False;
    noTrapCores: forall p, In p cores -> @hasTrap p = false;
    trapCore: CoreConfigParams;
    trapCoreMemSize: forall p, In p cores -> @LgNumMemBytes (@memParams p) = @LgNumMemBytes (@memParams trapCore);
    disjointTrapCore: forall x p, In p cores -> InBoundsInit x p -> InBoundsInit x trapCore -> False;
    sameMemTrapCore: forall x p,
      In p cores -> InBoundsInit x p ->
      evalExpr (Var type (SyntaxKind (Array _ (Bit 8))) (@memInit (@memParams trapCore)) @[Const _ x])%kami_expr =
        evalExpr (Var type (SyntaxKind (Array _ (Bit 8)))(@memInit (@memParams p)) @[Const _ x])%kami_expr;
    trapCoreHasTrap: @hasTrap trapCore = true;
  }.
