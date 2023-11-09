Require Import Kami.AllNotations.

Import ListNotations.

Section Lib.
  Variable ty: Kind -> Type.
  Definition Trunc32Signed m n (e: Bit n @# ty) :=
    SignExtendTruncLsb m (ZeroExtendTruncLsb 32 e).

  Definition Trunc32Unsigned m n (e: Bit n @# ty) :=
    ZeroExtendTruncLsb m (ZeroExtendTruncLsb 32 e).

  Definition StaticIf (filter : bool) (pred: Bool @# ty) k (tExpr fExpr: k @# ty) :=
    if filter then ITE pred tExpr fExpr else fExpr.
End Lib.

