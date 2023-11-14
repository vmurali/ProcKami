Require Import Kami.AllNotations.

Import ListNotations.

Section Lib.
  Variable ty: Kind -> Type.
  Definition StaticIf (filter : bool) (pred: Bool @# ty) k (tExpr fExpr: k @# ty) :=
    if filter then ITE pred tExpr fExpr else fExpr.

  Definition prevFinVal n (i: Fin.t (S n)) :=
    match i with
    | Fin.F1 _ => Fin.F1
    | Fin.FS _ j => L_R 1 j
    end.

  Definition TruncToSizeSigned sz m n (e: Bit n @# ty) :=
    SignExtendTruncLsb m (ZeroExtendTruncLsb sz e).

  Definition TruncToSizeUnsigned sz m n (e: Bit n @# ty) :=
    ZeroExtendTruncLsb m (ZeroExtendTruncLsb sz e).

  Definition ShuffleArray n k (inp: Array n k @# ty) m (inpStart: Bit m @# ty) : Array n k @# ty :=
    BuildArray (fun i => ReadArray inp (CABit Add [Const _ (natToWord _ (FinFun.Fin2Restrict.f2n i)); inpStart])).

  Definition TruncToDynamicSizeArrayUnsigned n k (a: Array n k @# ty) m (sz: Bit m @# ty) :=
    BuildArray
      (fun i =>
         ITE (BinBitBool (LessThan _) (Const _ (natToWord _ (FinFun.Fin2Restrict.f2n i))) sz)
           (ReadArrayConst a i)
           (Const ty Default)).

  Definition TruncToDynamicSizeArraySigned n width (a: Array n (Bit width) @# ty) m (sz: Bit m @# ty) :=
    BuildArray
      (fun i =>
         ITE (BinBitBool (LessThan _) (Const _ (natToWord _ (FinFun.Fin2Restrict.f2n i))) sz)
           (ReadArrayConst a i)
           (ITE (unpack Bool (ZeroExtendTruncMsb 1
                                (ReadArray a (CABit Add [sz; Const _ (wones m) ]))))
              (Const ty (wones width)) (Const ty (wzero width)))).
End Lib.

