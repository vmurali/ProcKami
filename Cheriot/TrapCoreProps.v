Require Import Kami.AllNotations.
Require Import ProcKami.Cheriot.Lib ProcKami.Cheriot.Types ProcKami.Cheriot.CoreConfig.
Require Import ProcKami.Cheriot.InstAssembly ProcKami.Cheriot.TrapHandler.

Section Props.
  Variable ty: Kind -> Type.
  Local Open Scope kami_expr.

  Definition hasRead (cap: Cap @# ty): Bool @# ty := getCapPerms cap @% "LD".
  Definition hasWrite (cap: Cap @# ty): Bool @# ty := getCapPerms cap @% "SD".
  Definition hasMC (cap: Cap @# ty): Bool @# ty := getCapPerms cap @% "MC".

  Definition CurrPlusSizeInBounds (cap: FullCapWithTag @# ty) sz : Bool ## ty :=
    ( LETE range : _ <- getCapBaseTop (rmTag cap);
      LETC baseBound : Bool <- #range @% "base" >= cap @% "val";
      LETC topBound : Bool <- (ZeroExtend 1 (cap @% "val") + $sz) <= #range @% "top";
      RetE (cap @% "tag" && #baseBound && #topBound )).

  Definition SubArrayMatch k n (f: type (Array (Nat.pow 2 n) k)) m (g: type (Array (Nat.pow 2 m) k))
    (start: type (Bit n)) :=
    forall i, (0 <= i)%nat -> (i < Nat.pow 2 m)%nat ->
              evalExpr (###f@[###start + $i]) = evalExpr (###g@[Const type (natToWord m i)]).
End Props.

Section TrapCoreSpec.
  Context `{coreConfigParams: CoreConfigParams}.
  Instance memParamsInst: MemParams := @memParams coreConfigParams.
  Local Open Scope kami_expr.

  Local Notation MemVar x := (Var type (SyntaxKind (Array _ FullCapWithTag)) x).

  Record TrapCoreSpec := {
      numCoresWord: word Imm12Sz;
      trapCoreHasTrap: hasTrap = true;
      mtccValXlen := wcombine mtccVal (wzero 2) : type Addr;
      mtccValidThm: MtccValid mtccCap mtccValXlen trapHandlerSize;
      mtdcValXlen := wcombine mtdcVal (wzero 3) : type Addr;
      mtdcValidThm: MtdcValid mtdcCap mtdcValXlen (MtdcTotalSize numCoresWord);
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
      currReadWriteMc: evalExpr (hasRead (rmTag curr @% "cap") && hasWrite (rmTag curr @% "cap") &&
                                   hasMC (rmTag curr @% "cap")) = true;
      mTimeCap: type FullCapWithTag;
      mTimeCmpCap: type FullCapWithTag;
      mTimeCapEq: mTimeCap = (evalExpr ((MemVar memInit) @[###mtdcValXlen]));
      mTimeCmpCapEq: mTimeCmpCap = (evalExpr ((MemVar memInit) @[###mtdcValXlen + $8]));
      mTimeSize: evalLetExpr (CurrPlusSizeInBounds ###mTimeCap 8) = true;
      mTimeCmpSize: evalLetExpr (CurrPlusSizeInBounds ###mTimeCmpCap 4) = true;
      mTimeRead: evalExpr (hasRead (###mTimeCap @% "cap")) = true;
      mTimeCmpReadWrite: evalExpr (hasRead (###mTimeCap @% "cap") && hasWrite (###mTimeCmpCap @% "cap")) = true;
      mtdcCapReadWriteMc: evalExpr (hasRead ###mtdcCap && hasWrite ###mtdcCap && hasMC ###mtdcCap) = true;
      (* mtdcDominatesCurr: DominatingCapsSingle [mtdcFullCap] (evalExpr (rmTag curr)); *)

    }.
End TrapCoreSpec.

 (*
 Initialize memory with trap handler (at mtcc) and trap data (at mtdc)
 *)
