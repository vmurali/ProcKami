Require Import Kami.AllNotations.
Require Import ProcKami.Cheriot.Lib ProcKami.Cheriot.Types ProcKami.Cheriot.CoreConfig.

Section InBoundsTy.
  Variable ty: Kind -> Type.
  Variable x inCap inVal: Bit 32 @# ty.

  Local Open Scope kami_expr.

  Let inRange := capBaseTop inCap inVal.

  Definition inBounds :=
    ( LETE inRangeVal <- inRange;
      RetE ((x >= #inRangeVal @% "base") && (ZeroExtend 1 x < #inRangeVal @% "top"))).

  Definition systemAccess :=
    ( LETE perms <- capPerms inCap;
      RetE (#perms @% "SR") ).
End InBoundsTy.

Section InBoundsInits.
  Variable x: word 32.
  Variable rfInit: Fin.t 32 -> type FullCapWithTagKind.
  Variable capPcInit: word 32.
  Variable valPcInit: word 32.

  Local Open Scope kami_expr.

  Definition InBoundsRf :=
    exists i, evalLetExpr (inBounds (Const _ x)
                             (Var type (SyntaxKind _) (rfInit i) @% "cap")
                             (Var type (SyntaxKind _) (rfInit i) @% "val")) = true.
  Definition InBoundsPc :=
    evalLetExpr (inBounds (Const _ x) (Const _ capPcInit) (Const _ valPcInit)) = true.

  Definition SystemAccessRf :=
    exists i, evalLetExpr (systemAccess (Var type (SyntaxKind _) (rfInit i) @% "cap")) = true.

  Definition SystemAccessPc :=
    evalLetExpr (systemAccess (Const _ capPcInit)) = true.
End InBoundsInits.

Section InBoundsCoreConfig.
  Variable x: word 32.
  Variable p: CoreConfigParams.
  Definition InBoundsInit := InBoundsRf x (@regsInitVal p) \/ InBoundsPc x (@pcCapInitVal p) (@pcValInitVal p).
  Definition SystemAccessInit := SystemAccessRf (@regsInitVal p) \/ SystemAccessPc (@pcCapInitVal p).
End InBoundsCoreConfig.

Record SpecIsolation := {
    cores: list CoreConfigParams;
    disjointNamesCores: NoDup (map (@prefix) cores);
    disjointBoundsCores: forall x p, In p cores -> InBoundsInit x p -> forall q,
                                         In q cores -> InBoundsInit x q -> @prefix p <> @prefix q -> False;
    noScrAccessCores: forall p, In p cores -> SystemAccessInit p -> False;
    noTrapCores: forall p, In p cores -> @hasTrapVal p = false;
    trapCore: CoreConfigParams;
    trapCoreMemSize: forall p, In p cores -> @LgNumMemBytesVal p = @LgNumMemBytesVal trapCore;
    disjointTrapCore: forall x p, In p cores -> InBoundsInit x p -> InBoundsInit x trapCore -> False;
    sameMemTrapCore: forall x p,
      In p cores -> InBoundsInit x p ->
      evalExpr (Var type (SyntaxKind (Array _ (Bit 8))) (@memInitVal trapCore) @[Const _ x])%kami_expr =
        evalExpr (Var type (SyntaxKind (Array _ (Bit 8)))(@memInitVal p) @[Const _ x])%kami_expr;
    trapCoreHasTrap: @hasTrapVal trapCore = true;
  }.
