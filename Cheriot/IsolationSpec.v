Require Import Kami.AllNotations.
Require Import ProcKami.Cheriot.Lib ProcKami.Cheriot.Types ProcKami.Cheriot.CoreConfig.

Section InBoundsPermsTy.
  Variable ty: Kind -> Type.
  Local Open Scope kami_expr.

  Section InBoundsPerms.
    Variable x: Addr @# ty.
    Variable cap: FullCap @# ty.

    Definition InBoundsAddr :=
      ( LETE inRangeVal <- getCapBaseTop cap;
        RetE ((x >= #inRangeVal @% "base") && (ZeroExtend 1 x < #inRangeVal @% "top"))).

    Definition InBoundsPermsAddr :=
      ( LETC perms <- getCapPerms (cap @% "cap");
        LETE inBounds <- InBoundsAddr;
        RetE ((#perms @% "LD" || #perms @% "SD") && #inBounds)).
  End InBoundsPerms.

  Section Subset.
    (* c1 is a subset of c2 *)
    Variable c1: FullCap @# ty.
    Variable c2: FullCap @# ty.

    Definition SubsetCap :=
      ( LETE range1 <- getCapBaseTop c1;
        LETE range2 <- getCapBaseTop c2;
        LETC perms1 <- getCapPerms (c1 @% "cap");
        LETC perms2 <- getCapPerms (c2 @% "cap");
        LETC permsSub <- isSubsetPerms #perms1 #perms2;
        RetE (#permsSub && (#range1 @% "base" >= #range2 @% "base") && (#range1 @% "top" <= #range2 @% "top"))).
  End Subset.
End InBoundsPermsTy.

Section Dominating.
  Local Open Scope kami_expr.

  Definition DominatingCaps (l: list (type FullCap)) n (arr: type (Array n FullCapWithTag)) :=
    forall sz (idx: type (Bit sz)),
      existsb (fun dc =>
                 evalLetExpr (LETC testCap <- ###arr@[###idx];
                              LETE isSubsetCap <- SubsetCap (rmTag ###testCap) ###dc;
                              RetE (!(###testCap @% "tag") || ###isSubsetCap))) l = true.

  Definition DominatingCapsPc (l: list (type FullCap)) (pcc: type FullCap) :=
    existsb (fun dc => evalLetExpr (SubsetCap ###pcc ###dc)) l = true.
    
  Definition DominatingCapsOverlap (l1 l2: list (type FullCap)) :=
    exists (addr: type Addr), (existsb (fun c => evalLetExpr (InBoundsPermsAddr ###addr ###c)) l1) = true /\
                                (existsb (fun c => evalLetExpr (InBoundsPermsAddr ###addr ###c)) l2) = true.
End Dominating.

Section IsolationSpec.
  Local Open Scope kami_expr.
  Record IsolationSpec := {
      cores: list (CoreConfigParams * list (type FullCap));
      numCoresWord: word Imm12Sz;
      numCoresSame: wordVal _ numCoresWord = Z.of_nat (length cores);
      procNameLength: nat;
      coresNameLengthEq: forall c, In c cores -> String.length (@procName (fst c)) = procNameLength;
      disjointCoreNames: NoDup (map (fun c => @procName (fst c)) cores);
      coreDominatingMemCaps: forall c, In c cores -> DominatingCaps (snd c) (@memInit (@memParams (fst c)));
      coreDominatingRegCaps: forall c, In c cores -> DominatingCaps (snd c) (@regsInit (fst c));
      coreDominatingPcc: forall c,
        In c cores ->
        DominatingCapsPc (snd c)
          (evalExpr (STRUCT { "cap" ::= Const _ (convTypeToConst (@pcCapInit (fst c)));
                              "val" ::= Const _ (wcombine (@pcValInit (fst c)) (wzero 2))}));
      coreNoTrap: forall c, In c cores -> @hasTrap (fst c) = false;
      trapCore: CoreConfigParams;
      trapCoreMemSize: forall c, In c cores ->
                                 @LgNumMemBytes (@memParams (fst c)) = @LgNumMemBytes (@memParams trapCore);
      sameMemTrapCore: forall x c dc,
        In c cores -> In dc (snd c) -> evalLetExpr (InBoundsAddr (###x) (###dc)) = true ->
        evalExpr (Var type (SyntaxKind (Array _ FullCapWithTag))(@memInit (@memParams trapCore)) @[###x]) =
          evalExpr (Var type (SyntaxKind (Array _ FullCapWithTag))(@memInit (@memParams (fst c))) @[###x]);
      trapCoreHasTrap: @hasTrap trapCore = true;
    }.
End IsolationSpec.

(*
- Initialize memory with trap handler (at mtcc) and trap data (at mtdc)
- Make sure mtcc can hold size of trapHandler code
- Make sure mtdc can hold 24 + NumRegs*8*(wordVal _ numCoresWord)
- mtcc and mtdc are disjoint from any of the dominating caps
- mtcc and mtdc are disjoint from each other
 *)
