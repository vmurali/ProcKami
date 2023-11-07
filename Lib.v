Require Import Kami.AllNotations.

Import ListNotations.

Section Lib.
  Variable ty: Kind -> Type.
  Definition Trunc32Signed m n (e: Bit n @# ty) :=
    SignExtendTruncLsb m (ZeroExtendTruncLsb 32 e).

  Definition Trunc32Unsigned m n (e: Bit n @# ty) :=
    ZeroExtendTruncLsb m (ZeroExtendTruncLsb 32 e).

  Local Open Scope kami_expr.
  Definition Sub n (e1 e2: Bit n @# ty) :=
    e1 + ~e2 + $1.

  Definition isNotZero n (e: Bit n @# ty) := unpack Bool (UniBit (UOr n) e).
  Definition isZero n (e: Bit n @# ty) := !isNotZero e.

  Definition StaticIf (filter : bool) (pred: Bool @# ty) k (tExpr fExpr: k @# ty) :=
    if filter then ITE pred tExpr fExpr else fExpr.

  Definition mkPair A B (a: A @# ty) (b: B @# ty) : Pair A B @# ty :=
    STRUCT { "fst" ::= a; "snd" ::= b }.

End Lib.

