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
End InBoundsPermsTy.

Section Props.
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

  Definition DominatingCapsNoOverlap (l1 l2: list (type FullCap)) := not (DominatingCapsOverlap l1 l2).

  Definition hasRead (cap: type Cap) := evalExpr ((getCapPerms ###cap) @% "LD") = true.
  Definition hasWrite (cap: type Cap) := evalExpr ((getCapPerms ###cap) @% "SD") = true.
  Definition hasMC (cap: type Cap) := evalExpr ((getCapPerms ###cap) @% "MC") = true.

  Definition AddrPlusSizeInBounds (cap: type Cap) (addr: type Addr) sz :=
    evalLetExpr ( LETE range : _ <- getCapBaseTop (STRUCT {"cap" ::= ###cap; "val" ::= ###addr});
                  LETC baseBound <- (###range @% "base") <= ###addr;
                  LETC topBound <- (ZeroExtend 1 ###addr + (Const type (ZToWord _ sz))) <= (###range @% "top");
                  RetE (###baseBound && ###topBound )) = true.

  Definition SubArrayMatch k n (f: type (Array (Nat.pow 2 n) k)) m (g: type (Array (Nat.pow 2 m) k))
    (start: type (Bit n)) :=
    forall i, (0 <= i)%nat -> (i < Nat.pow 2 m)%nat ->
              evalExpr (###f@[###start + $i]) = evalExpr (###g@[Const type (natToWord m i)]).

  Definition MtccValid (mtccCap: type Cap) (mtccVal: type Addr) mtccSize :=
    evalLetExpr ( LETC perms <- getCapPerms ###mtccCap;
                  LETC sealed <- isCapSealed ###mtccCap;
                  LETC aligned <- isZero (UniBit (TruncLsb 2 _) ###mtccVal);
                  LETE baseTop <- getCapBaseTop (STRUCT {"cap" ::= ###mtccCap; "val" ::= ###mtccVal});
                  LETC baseBound <- ###mtccVal >= (###baseTop @% "base");
                  LETC mtccSizeConst <- Const type (ZToWord _ mtccSize);
                  LETC topBound <- (ZeroExtend 1 ###mtccVal + ###mtccSizeConst <= (###baseTop @% "top"));
                  RetE ((###perms @% "EX") && (###perms @% "SR") && !###sealed && ###aligned
                        && (###baseBound && ###topBound))) = true.
End Props.

Section TrapCoreSpec.
  Context `{coreConfigParams: CoreConfigParams}.
  Instance memParamsInst: MemParams := @memParams coreConfigParams.
  Variable numCoresWord: word Imm12Sz.
  Local Open Scope kami_expr.

  Local Notation MemVar x := (Var type (SyntaxKind (Array _ FullCapWithTag)) x).

  Record TrapCoreSpec := {
      trapCoreHasTrap: hasTrap = true;
      mtccValXlen := wcombine mtccVal (wzero 2) : type Addr;
      mtccValidThm: MtccValid mtccCap mtccValXlen trapHandlerSize;
      mtdcValXlen := wcombine mtdcVal (wzero 3) : type Addr;
      mtdcValidThm: AddrPlusSizeInBounds mtdcCap mtdcValXlen (MtdcTotalSize numCoresWord);
      mtccFullCap := evalExpr (STRUCT { "cap" ::= ###mtccCap;
                                        "val" ::= ###mtccValXlen });
      mtdcFullCap := evalExpr (STRUCT { "cap" ::= ###mtdcCap;
                                        "val" ::= ###mtdcValXlen });
      curr := (MemVar memInit) @[###mtdcValXlen + $16];
      currTagged: evalExpr (curr @% "tag") = true;
      currCapIsMtdcCap: evalExpr (curr @% "cap") = mtdcCap;
      currAddr: exists n, (n < wordVal _ numCoresWord)%Z /\
                            evalExpr (curr @% "val") =
                              wadd mtdcValXlen (ZToWord Xlen (24 + (n * (Z.of_nat NumRegs * 8))));
      currReadWriteMc: hasRead (evalExpr (curr @% "cap")) /\ hasWrite (evalExpr (curr @% "cap")) /\
                         hasMC (evalExpr (curr @% "cap"));
      mTimeCap: type FullCapWithTag;
      mTimeCmpCap: type FullCapWithTag;
      mTimeCapEq: mTimeCap = (evalExpr ((MemVar memInit) @[###mtdcValXlen]));
      mTimeCmpCapEq: mTimeCmpCap = (evalExpr ((MemVar memInit) @[###mtdcValXlen + $8]));
      mTimeTag: evalExpr (###mTimeCap @% "tag") = true;
      mTimeCmpTag: evalExpr (###mTimeCmpCap @% "tag") = true;
      mTimeSize: AddrPlusSizeInBounds (evalExpr (###mTimeCap @% "cap")) (evalExpr (###mTimeCap @% "val")) 8;
      mTimeCmpSize: AddrPlusSizeInBounds (evalExpr (###mTimeCmpCap @% "cap")) (evalExpr (###mTimeCmpCap @% "val")) 4;
      mTimeRead: hasRead (evalExpr (###mTimeCap @% "cap"));
      mTimeCmpReadWrite: hasRead (evalExpr (###mTimeCmpCap @% "cap")) /\
                           hasWrite (evalExpr (###mTimeCmpCap @% "cap"));
      mtdcCapReadWriteMc: hasRead mtdcCap /\ hasWrite mtdcCap /\ hasMC mtdcCap;
      mtdcDominatesCurr: DominatingCapsSingle [mtdcFullCap] (evalExpr (rmTag curr))
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
                              "val" ::= Const _ (wcombine (@pcValInit (fst c)) (wzero 2))}));
      coreNoTrap: forall c, In c cores -> @hasTrap (fst c) = false;
      trapCore: CoreConfigParams;
      trapCoreMemSize: forall c, In c cores ->
                                 @LgNumMemBytes (@memParams (fst c)) = @LgNumMemBytes (@memParams trapCore);
      sameMemTrapCore: forall x c dc,
        In c cores -> In dc (snd c) -> evalLetExpr (InBoundsAddr (###x) (###dc)) = true ->
        evalExpr (MemVar (@memInit (@memParams trapCore)) @[###x]) =
          evalExpr (MemVar (@memInit (@memParams (fst c))) @[###x]);

      trapCoreProps: @TrapCoreSpec trapCore numCoresWord;
    }.
End IsolationSpec.

(*
- Take care of sealed
- Fix curr vs mtdc
- Fix MtccValid
- Initialize memory with trap handler (at mtcc) and trap data (at mtdc)
*)
