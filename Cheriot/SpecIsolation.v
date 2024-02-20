Require Import Kami.AllNotations.
Require Import ProcKami.Cheriot.Lib ProcKami.Cheriot.Types ProcKami.Cheriot.CoreConfig.

Section InBoundsTy.
  Variable ty: Kind -> Type.
  Variable x inCap inVal: Bit 32 @# ty.

  Let inRange := capBaseTop inCap inVal.

  Definition inBounds :=
    ( LETE inRangeVal <- inRange;
      RetE ((x >= #inRangeVal @% "base") && (ZeroExtend 1 x < #inRangeVal @% "top")))%kami_expr.

  Definition systemAccess :=
    ( LETE perms <- capPerms inCap;
      RetE (#perms @% "SR") )%kami_expr.
End InBoundsTy.

Section InBoundsInits.
  Variable x: word 32.
  Variable rfInit: Fin.t 32 -> type FullCapWithTagKind.
  Variable capPcInit: word 32.
  Variable valPcInit: word 32.

  Definition InBoundsRf :=
    exists i, evalLetExpr (inBounds (Const _ x)
                             (Var type (SyntaxKind _) (rfInit i) @% "cap")
                             (Var type (SyntaxKind _) (rfInit i) @% "val"))%kami_expr = true.
  Definition InBoundsPc :=
    evalLetExpr (inBounds (Const _ x) (Const _ capPcInit) (Const _ valPcInit)) = true.
End InBoundsInits.

Section InBoundsCoreConfig.
  Variable x: word 32.
  Variable p: CoreConfigParams.
  Definition InBoundsInit := InBoundsRf x (@regsInitVal p) \/ InBoundsPc x (@pcCapInitVal p) (@pcValInitVal p).
End InBoundsCoreConfig.

Record SpecIsolation := {
    cores: list CoreConfigParams;
    disjointNames: NoDup (map (@prefix) cores);
    disjointBounds: forall x p, In p cores -> InBoundsInit x p -> forall q,
                                    In q cores -> InBoundsInit x q -> @prefix p <> @prefix q -> False;
    noScrPcAccess: forall p, In p cores -> evalLetExpr (systemAccess (Const _ (@pcCapInitVal p))) = false;
    noScrRfAccess: forall p, In p cores -> forall i,
        evalLetExpr (systemAccess (Var type (SyntaxKind _) (@regsInitVal p i) @% "cap"))%kami_expr = false;
    trapCore: CoreConfigParams;
    trapCoreMemSize: forall p, In p cores -> @LgNumMemBytesVal p = @LgNumMemBytesVal trapCore;
    disjointTrapCore: forall x p, In p cores -> InBoundsInit x p -> InBoundsInit x trapCore -> False;
    sameMem: forall x p,
      In p cores -> InBoundsInit x p ->
      evalExpr (Var type (SyntaxKind (Array _ (Bit 8))) (@memInitVal trapCore) @[Const _ x])%kami_expr =
        evalExpr (Var type (SyntaxKind (Array _ (Bit 8)))(@memInitVal p) @[Const _ x])%kami_expr;
    isTrap: @hasTrapVal trapCore = true;
    noTrapCores: forall p, In p cores -> @hasTrapVal p = false;
  }.
