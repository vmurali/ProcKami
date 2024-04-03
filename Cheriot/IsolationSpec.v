Require Import Kami.AllNotations.
Require Import ProcKami.Cheriot.Lib ProcKami.Cheriot.Types ProcKami.Cheriot.CoreConfig.

Section InBoundsTy.
  Variable ty: Kind -> Type.
  Local Open Scope kami_expr.

  Section InBounds.
    Variable x: Addr @# ty.
    Variable cap: FullCap @# ty.

    Definition InBoundsAddr :=
      ( LETE inRangeVal <- getCapBaseTop cap;
        RetE ((x >= #inRangeVal @% "base") && (ZeroExtend 1 x < #inRangeVal @% "top"))).
  End InBounds.

  Section Subset.
    (* c1 is a subset of c2 *)
    Variable c1: FullCapWithTag @# ty.
    Variable c2: FullCap @# ty.

    Definition SubsetCap :=
      ( LETE range1 <- getCapBaseTop (rmTag c1);
        LETE range2 <- getCapBaseTop c2;
        LETC perms1 <- getCapPerms (c1 @% "cap");
        LETC perms2 <- getCapPerms (c2 @% "cap");
        LETC permsSub <- isSubsetPerms #perms1 #perms2;
        RetE (#permsSub && (#range1 @% "base" >= #range2 @% "base") && (#range1 @% "top" <= #range2 @% "top"))).
  End Subset.
End InBoundsTy.

Section Dominating.
  Local Open Scope kami_expr.

  Definition DominatingCaps (l: list (type FullCap)) n (arr: type (Array n FullCapWithTag)) :=
    forall addr: type Addr,
      existsb (fun dc =>
                 evalLetExpr (LETC testCap <- ###arr@[###addr];
                              LETE isSubsetCap <- SubsetCap ###testCap ###dc;
                              RetE (!(###testCap @% "tag") || ###isSubsetCap))) l = true.

  Definition DominatingCapsOverlap (l1 l2: list (type FullCap)) :=
    exists (addr: type Addr), (existsb (fun c => evalLetExpr (InBoundsAddr ###addr ###c)) l1) = true /\
                                (existsb (fun c => evalLetExpr (InBoundsAddr ###addr ###c)) l2) = true.
End Dominating.

(*
Record IsolationSpec := {
    cores: list (CoreConfigParams * list (type FullCap));
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
*)
