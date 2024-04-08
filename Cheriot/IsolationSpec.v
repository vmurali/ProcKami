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
        RetE ((#perms @% "EX" || #perms @% "LD" || #perms @% "SD") && #inBounds)).
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

Section Props.
  Local Open Scope kami_expr.

  Definition DominatingCaps (l: list (type FullCap)) n (arr: type (Array n FullCapWithTag)) :=
    forall sz (idx: type (Bit sz)),
      existsb (fun dc => evalLetExpr (LETC testCap <- ###arr@[###idx];
                                      LETE isSubsetCap <- SubsetCap (rmTag ###testCap) ###dc;
                                      RetE (!(###testCap @% "tag") || ###isSubsetCap))) l = true.

  Definition DominatingCapsSingle (l: list (type FullCap)) (cap: type FullCap) :=
    existsb (fun dc => evalLetExpr (SubsetCap ###cap ###dc)) l = true.
    
  Definition CapsOverlap (l1 l2: list (type FullCap)) :=
    exists (addr: type Addr), (existsb (fun c => evalLetExpr (InBoundsAddr ###addr ###c)) l1) = true /\
                                (existsb (fun c => evalLetExpr (InBoundsAddr ###addr ###c)) l2) = true.

  Definition CapsNoOverlap (l1 l2: list (type FullCap)) := not (CapsOverlap l1 l2).

  Definition hasPerms (cap: type Cap) (perms: type CapPerms) :=
    evalLetExpr ( LETC capPerms <- getCapPerms ###cap;
                  RetE (isSubsetPerms ###perms ###capPerms)) = true.

  Definition AddrPlusSizeInBounds (cap: type Cap) (addr: type Addr) sz :=
    evalLetExpr ( LETE range : _ <- getCapBaseTop (STRUCT {"cap" ::= ###cap; "val" ::= ###addr});
                  LETC baseBound <- (###range @% "base") <= ###addr;
                  LETC topBound <- (ZeroExtend 1 ###addr + (Const type (ZToWord _ sz))) <= (###range @% "top");
                  RetE (###baseBound && ###topBound )) = true.

  Definition SubArrayMatch k n (f: type (Array (Nat.pow 2 n) k)) m (g: type (Array (Nat.pow 2 m) k))
    (start: type (Bit n)) :=
    forall i, (i < Nat.pow 2 m)%nat ->
              evalExpr (###f@[###start + $i]) = evalExpr (###g@[Const type (natToWord m i)]).
End Props.

Section TrapCoreSpec.
  Context `{coreConfigParams: CoreConfigParams}.
  Instance memParamsInst: MemParams := @memParams coreConfigParams.
  Variable numCoresWord: word Imm12Sz.
  Local Open Scope kami_expr.

  Local Notation MemVar x := (Var type (SyntaxKind (Array _ FullCapWithTag)) x).

  Record TrapCoreSpec := {
      trapCoreHasTrap: hasTrap = true;

      mtccValidBounds: AddrPlusSizeInBounds mtccCap mtccVal trapHandlerSize;
      mtccValidPerms: hasPerms mtccCap (evalExpr (STRUCT { "U0" ::= Const type false;
                                                           "SE" ::= Const type false;
                                                           "US" ::= Const type false;
                                                           "EX" ::= Const type true;
                                                           "SR" ::= Const type true;
                                                           "MC" ::= Const type false;
                                                           "LD" ::= Const type false;
                                                           "SL" ::= Const type false;
                                                           "LM" ::= Const type false;
                                                           "SD" ::= Const type false;
                                                           "LG" ::= Const type false;
                                                           "GL" ::= Const type false }));
      mtccNotSealed: evalExpr (isCapSealed ###mtccCap) = false;
                                            
      mtdcValidBounds: AddrPlusSizeInBounds mtdcCap mtdcVal (MtdcTotalSize numCoresWord);

      curr := (MemVar memInit) @[###mtdcVal + $16];
      currTagged: evalExpr (curr @% "tag") = true;
      currCapIsMtdcCap: evalExpr (curr @% "cap") = mtdcCap;
      currAddr: exists n, wltu n numCoresWord = true /\
                            evalExpr (curr @% "val") = wadd mtdcVal (ZToWord _ (MtdcTotalSize n));
      currValidBounds: hasPerms mtdcCap (evalExpr (STRUCT { "U0" ::= Const type false;
                                                            "SE" ::= Const type false;
                                                            "US" ::= Const type false;
                                                            "EX" ::= Const type false;
                                                            "SR" ::= Const type false;
                                                            "MC" ::= Const type true;
                                                            "LD" ::= Const type true;
                                                            "SL" ::= Const type true;
                                                            "LM" ::= Const type true;
                                                            "SD" ::= Const type true;
                                                            "LG" ::= Const type true;
                                                            "GL" ::= Const type true }));
      currNotSealed: evalExpr (isCapSealed ###mtdcCap) = false;
      
      mTimeCap := (MemVar memInit) @[###mtdcVal];
      mTimeTag: evalExpr (mTimeCap @% "tag") = true;
      mTimeSize: AddrPlusSizeInBounds (evalExpr (mTimeCap @% "cap")) (evalExpr (mTimeCap @% "val")) 8;
      mTimeValidPerms: hasPerms (evalExpr (mTimeCap @% "cap"))
                         (evalExpr (STRUCT { "U0" ::= Const type false;
                                             "SE" ::= Const type false;
                                             "US" ::= Const type false;
                                             "EX" ::= Const type false;
                                             "SR" ::= Const type false;
                                             "MC" ::= Const type false;
                                             "LD" ::= Const type true;
                                             "SL" ::= Const type false;
                                             "LM" ::= Const type false;
                                             "SD" ::= Const type false;
                                             "LG" ::= Const type false;
                                             "GL" ::= Const type false }));
      mTimeNotSealed: evalExpr (isCapSealed (mTimeCap @% "cap")) = false;

      mTimeCmpCap := (MemVar memInit) @[###mtdcVal + $8];
      mTimeCmpTag: evalExpr (mTimeCmpCap @% "tag") = true;
      mTimeCmpSize: AddrPlusSizeInBounds (evalExpr (mTimeCmpCap @% "cap")) (evalExpr (mTimeCmpCap @% "val")) 4;
      mTimeCmpValidPerms: hasPerms (evalExpr (mTimeCmpCap @% "cap"))
                            (evalExpr (STRUCT { "U0" ::= Const type false;
                                                "SE" ::= Const type false;
                                                "US" ::= Const type false;
                                                "EX" ::= Const type false;
                                                "SR" ::= Const type false;
                                                "MC" ::= Const type false;
                                                "LD" ::= Const type true;
                                                "SL" ::= Const type false;
                                                "LM" ::= Const type false;
                                                "SD" ::= Const type true;
                                                "LG" ::= Const type false;
                                                "GL" ::= Const type false }));
      mTimeCmpNotSealed: evalExpr (isCapSealed (mTimeCmpCap @% "cap")) = false;
    }.
End TrapCoreSpec.

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
                              "val" ::= Const _ (@pcValInit (fst c))}));
      coreNoTrap: forall c, In c cores -> @hasTrap (fst c) = false;
      
      trapCore: CoreConfigParams;
      trapCoreMemSize: forall c, In c cores ->
                                 @LgNumMemBytes (@memParams (fst c)) = @LgNumMemBytes (@memParams trapCore);
      sameMemTrapCore: forall x c dc,
        In c cores -> In dc (snd c) -> evalLetExpr (InBoundsAddr (###x) (###dc)) = true ->
        evalExpr (MemVar (@memInit (@memParams trapCore)) @[###x]) =
          evalExpr (MemVar (@memInit (@memParams (fst c))) @[###x]);

      trapCoreProps: @TrapCoreSpec trapCore numCoresWord;

      noOverlapCaps: ForallOrdPairs CapsNoOverlap
                       ([evalExpr (STRUCT { "cap" ::= ###(@mtccCap trapCore);
                                            "val" ::= ###(@mtccVal trapCore) })] ::
                          [evalExpr (STRUCT { "cap" ::= ###(@mtdcCap trapCore);
                                              "val" ::= ###(@mtdcVal trapCore) })] ::
                          [evalExpr (rmTag (mTimeCap trapCoreProps))] ::
                          [evalExpr (rmTag (mTimeCmpCap trapCoreProps))] :: map snd cores);

      contexts := map (fun '(c, _) => fun i => match i with
                                               | Fin.F1 _ => evalExpr (STRUCT { "tag" ::= Const type true;
                                                                                "cap" ::= ###(@pcCapInit c);
                                                                                "val" ::= ###(@pcValInit c) })
                                               | _ => regsInit i
                                               end) cores;

      contextsInMtdc: forall i: Fin.t (length contexts),
        SubArrayMatch (@memInit (@memParams trapCore)) RegIdSz (nth_Fin contexts i)
          (natToWord _ (FinFun.Fin2Restrict.f2n i))
    }.
End IsolationSpec.

(*
- Initialize memory with trap handler (at mtcc)
*)
