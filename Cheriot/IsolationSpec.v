Require Import Kami.AllNotations.
Require Import ProcKami.Cheriot.Lib ProcKami.Cheriot.Types ProcKami.Cheriot.CoreConfig.
Require Import ProcKami.Cheriot.InstAssembly ProcKami.Cheriot.TrapHandler.

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

  Definition hasRead (cap: Cap @# ty): Bool @# ty := getCapPerms cap @% "LD".
  Definition hasWrite (cap: Cap @# ty): Bool @# ty := getCapPerms cap @% "SD".
  Definition hasMC (cap: Cap @# ty): Bool @# ty := getCapPerms cap @% "MC".

  Definition CurrPlusSizeInBounds (cap: FullCap @# ty) sz : Bool ## ty :=
    ( LETE range : _ <- getCapBaseTop cap;
      LETC baseBound : Bool <- #range @% "base" >= cap @% "val";
      LETC topBound : Bool <- (ZeroExtend 1 (cap @% "val") + $sz) <= #range @% "top";
      RetE (#baseBound && #topBound )).

End InBoundsPermsTy.

Definition CurrPlusSizeInBoundsProp (cap: type FullCap) sz :=
  evalLetExpr (CurrPlusSizeInBounds ###cap sz)%kami_expr = true.

Section Dominating.
  Local Open Scope kami_expr.

  Definition DominatingCaps (l: list (type FullCap)) n (arr: type (Array n FullCapWithTag)) :=
    forall sz (idx: type (Bit sz)),
      existsb (fun dc =>
                 evalLetExpr (LETC testCap <- ###arr@[###idx];
                              LETE isSubsetCap <- SubsetCap (rmTag ###testCap) ###dc;
                              RetE (!(###testCap @% "tag") || ###isSubsetCap))) l = true.

  Definition DominatingCapsSingle (l: list (type FullCap)) (cap: type FullCap) :=
    existsb (fun dc => evalLetExpr (SubsetCap ###cap ###dc)) l = true.
    
  Definition DominatingCapsOverlap (l1 l2: list (type FullCap)) :=
    exists (addr: type Addr), (existsb (fun c => evalLetExpr (InBoundsPermsAddr ###addr ###c)) l1) = true /\
                                (existsb (fun c => evalLetExpr (InBoundsPermsAddr ###addr ###c)) l2) = true.
End Dominating.

Definition DominatingCapsNoOverlap (l1 l2: list (type FullCap)) := ~ (DominatingCapsOverlap l1 l2).

Section IsolationSpec.
  Local Open Scope kami_expr.

  Local Notation MemVar x := (Var type (SyntaxKind (Array _ FullCapWithTag)) x).

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
        DominatingCapsSingle (snd c)
          (evalExpr (STRUCT { "cap" ::= Const _ (convTypeToConst (@pcCapInit (fst c)));
                              "val" ::= Const _ (wcombine (@pcValInit (fst c)) (wzero 2))}));
      coreNoTrap: forall c, In c cores -> @hasTrap (fst c) = false;
      trapCore: CoreConfigParams;
      trapCoreMemSize: forall c, In c cores ->
                                 @LgNumMemBytes (@memParams (fst c)) = @LgNumMemBytes (@memParams trapCore);
      sameMemTrapCore: forall x c dc,
        In c cores -> In dc (snd c) -> evalLetExpr (InBoundsAddr (###x) (###dc)) = true ->
        evalExpr (MemVar (@memInit (@memParams trapCore)) @[###x]) =
          evalExpr (MemVar (@memInit (@memParams (fst c))) @[###x]);
      trapCoreHasTrap: @hasTrap trapCore = true;
      mtccValXlen := wcombine (@mtccVal trapCore) (wzero 2) : type Addr;
      mtccValidThm: MtccValid (@mtccCap trapCore) mtccValXlen trapHandlerSize;
      mtdcValXlen := wcombine (@mtdcVal trapCore) (wzero 3) : type Addr;
      mtdcValidThm: MtdcValid (@mtdcCap trapCore) mtdcValXlen (MtdcTotalSize numCoresWord);
      mtccFullCap := evalExpr (STRUCT { "cap" ::= ###(@mtccCap trapCore);
                                        "val" ::= ###mtccValXlen });
      mtdcFullCap := evalExpr (STRUCT { "cap" ::= ###(@mtdcCap trapCore);
                                        "val" ::= ###mtdcValXlen });
      curr := (MemVar (@memInit (@memParams trapCore))) @[###mtdcValXlen + $16];
      currTagged: evalExpr (curr @% "tag") = true;
      currCapIsMtdcCap: evalExpr (curr @% "cap") = @mtdcCap trapCore;
      currAddr: exists n, (n < wordVal _ numCoresWord)%Z /\
                            evalExpr (curr @% "val") =
                              wadd mtdcValXlen (ZToWord Xlen (24 + (n * (Z.of_nat NumRegs * 8))));
      currReadWriteMc: evalExpr (hasRead (rmTag curr @% "cap") && hasWrite (rmTag curr @% "cap") &&
                                   hasMC (rmTag curr @% "cap")) = true;
      mtdcDominatesCurr: DominatingCapsSingle [mtdcFullCap] (evalExpr (rmTag curr));
      mTimeCap: type FullCap;
      mTimeCmpCap: type FullCap;
      mTimeCapEq: mTimeCap = (evalExpr (rmTag ((MemVar (@memInit (@memParams trapCore))) @[###mtdcValXlen])));
      mTimeCmpCapEq: mTimeCmpCap =
                       (evalExpr (rmTag ((MemVar (@memInit (@memParams trapCore))) @[###mtdcValXlen + $8])));
      mTimeSize: CurrPlusSizeInBoundsProp mTimeCap 8;
      mTimeCmpSize: CurrPlusSizeInBoundsProp mTimeCmpCap 4;
      mTimeRead: evalExpr (hasRead (###mTimeCap @% "cap")) = true;
      mTimeCmpReadWrite: evalExpr (hasRead (###mTimeCap @% "cap") && hasWrite (###mTimeCmpCap @% "cap")) = true;
      mtdcCapReadWriteMc: evalExpr (hasRead ###(@mtdcCap trapCore) && hasWrite ###(@mtdcCap trapCore) &&
                                      hasMC ###(@mtdcCap trapCore)) = true;
      disjointCaps: ForallOrdPairs DominatingCapsNoOverlap
                      ([mtccFullCap] :: [mtdcFullCap] :: [mTimeCap] :: [mTimeCmpCap] :: map snd cores)
    }.
End IsolationSpec.

Theorem test1 A (P: A -> Prop) : ~ (exists a, P a) -> (forall a, ~ P a).
Proof.
  intros.
  intro.
  assert (exists a, P a) by (exists a; auto).
  tauto.
Qed.

Theorem test2 A (P: A -> Prop) : (forall a, ~ P a) -> ~ (exists a, P a).
Proof.
  intros.
  intro.
  destruct H0.
  specialize (H x).
  tauto.
Qed.
  

  (*
 Initialize memory with trap handler (at mtcc) and trap data (at mtdc)
 *)
