Require Import Kami.AllNotations.
Require Import ProcKami.Cheriot.Lib ProcKami.Cheriot.Types ProcKami.Cheriot.CoreConfig.

Section InBoundsTy.
  Variable ty: Kind -> Type.
  Variable x : Addr @# ty.
  Variable cap: FullCapWithTag @# ty.

  Local Open Scope kami_expr.

  Definition inBounds :=
    ( LETE inRangeVal <- getCapBaseTop (rmTag cap);
      RetE (cap @% "tag" && (x >= #inRangeVal @% "base") && (ZeroExtend 1 x < #inRangeVal @% "top"))).

  Definition systemAccess :=
    ( LETC perms <- getCapPerms (cap @% "cap");
      RetE (cap @% "tag" && #perms @% "SR") ).
End InBoundsTy.

Section InBoundsInits.
  Variable x: word AddrSz.
  Variable rfInit: Fin.t NumRegs -> type FullCapWithTag.
  Variable pccInit: type FullCapWithTag.

  Local Open Scope kami_expr.

  Definition InBoundsRf :=
    exists i, evalLetExpr (inBounds (Const _ x) (Const _ (convTypeToConst (rfInit i)))) = true.

  Definition InBoundsPc :=
    evalLetExpr (inBounds (Const _ x) (Const _ (convTypeToConst pccInit))) = true.

  Definition SystemAccessRf :=
    exists i, evalLetExpr (systemAccess (Const _ (convTypeToConst (rfInit i)))) = true.

  Definition SystemAccessPc :=
    evalLetExpr (systemAccess (Const _ (convTypeToConst pccInit))) = true.
End InBoundsInits.

Section InBoundsCoreConfig.
  Variable x: word AddrSz.
  Variable p: CoreConfigParams.

  Let pccInit := evalExpr (STRUCT {"tag" ::= Const _ true ;
                                    "cap" ::= Const _ (convTypeToConst (@pcCapInit p)) ;
                                    "val" ::= Const _ (wcombine (@pcValInit p) (wzero 2)) })%kami_expr.
  
  Definition InBounds := InBoundsRf x (@regsInit p) \/ InBoundsPc x pccInit.

  Definition SystemAccess := SystemAccessRf (@regsInit p) \/ SystemAccessPc pccInit.
End InBoundsCoreConfig.

Record SpecIsolation := {
    cores: list CoreConfigParams;
    disjointNamesCores: NoDup (map (@procName) cores);
    disjointBoundsCores: forall x p, In p cores -> InBounds x p -> forall q,
                                         In q cores -> InBounds x q -> @procName p = @procName q;
    noScrAccessCores: forall p, In p cores -> SystemAccess p -> False;
    noTrapCores: forall p, In p cores -> @hasTrap p = false;
    trapCore: CoreConfigParams;
    trapCoreMemSize: forall p, In p cores -> @LgNumMemBytes (@memParams p) = @LgNumMemBytes (@memParams trapCore);
    disjointTrapCore: forall x p, In p cores -> InBounds x p -> InBounds x trapCore -> False;
    sameMemTrapCore: forall x p,
      In p cores -> InBounds x p ->
      evalExpr (Var type (SyntaxKind (Array _ (Bit 8))) (@memInit (@memParams trapCore)) @[Const _ x])%kami_expr =
        evalExpr (Var type (SyntaxKind (Array _ (Bit 8)))(@memInit (@memParams p)) @[Const _ x])%kami_expr;
    trapCoreHasTrap: @hasTrap trapCore = true;
  }.
