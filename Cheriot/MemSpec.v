Require Import Kami.AllNotations ProcKami.Cheriot.Lib ProcKami.Cheriot.Types.

Section MemSpec.
  Variable procName: string.
  Context `{memParams: MemParams}.
  
  Section ty.
    Variable ty: Kind -> Type.
    Local Open Scope kami_expr.
    Local Open Scope kami_action.

    Local Notation "@^ x" := ((procName ++ "_") ++ x)%string (at level 0).

    Section LoadStore.
      Variable pred: Bool @# ty.
      Variable addr: Addr @# ty.
      Variable size: MemSize @# ty.
      Variable isCap: Bool @# ty.
      Variable signed: Bool @# ty.
      Variable data: FullCapWithTag @# ty.
      
      Local Ltac dischargeDiv8 :=
        unfold NumBanks, FullCap, Cap, CapSz, Data; auto.

      Definition loadReqSpec: ActionT ty FullCapWithTag :=
        ( Read memArr : Array NumMemBytes (Bit 8) <- @^memArray;
          LET ldBytes <- readArrayConstSize addr #memArr NumBanks;
          LET ldSignVal <- (IF signed
                            then TruncToDynamicSizeArraySigned #ldBytes size
                            else TruncToDynamicSizeArrayUnsigned #ldBytes size);
          LET ldVal <- unpack FullCap (pack #ldSignVal);
          Read tags: Array NumMemBytes Bool <- @^tagArray;
          LET tagIdx <- ZeroExtendTruncLsb (Nat.log2_up NumMemBytes)
                          (TruncMsbTo (Xlen - Nat.log2_up NumBanks) (Nat.log2_up NumBanks) addr);
          LET tag <- ITE isCap (#tags@[#tagIdx]) $$false;
          Ret (STRUCT {
                   "tag" ::= #tag;
                   "cap" ::= #ldVal @% "cap";
                   "val" ::= #ldVal @% "val" } : FullCapWithTag @# ty)).

      Definition storeReqSpec: ActionT ty Void :=
        ( Read memArr : Array NumMemBytes (Bit 8) <- @^memArray;
          LET idxLsb <- TruncLsbTo (Nat.log2_up NumBanks) _ addr;
          LET straddle <- ZeroExtend 1 #idxLsb + size <= $NumBanks;
          LET tagIdx <- ZeroExtendTruncLsb (Nat.log2_up NumMemBytes)
                          (TruncMsbTo (Xlen - Nat.log2_up NumBanks) (Nat.log2_up NumBanks) addr);
          Read tags: Array NumMemBytes Bool <- @^tagArray;
          LET updTag <- #tags@[ #tagIdx <- ITE isCap (data @% "tag") $$false];
          (* #straddle implies !#isCap *)
          LET updTagPlus1 <- #updTag@[ #tagIdx + $1 <- ITE #straddle $$false (#updTag@[#tagIdx + $1])];
          LET stCapVal <- {< pack (data @% "cap"), (data @% "val") >};
          LET stBytes <- unpack (Array NumBanks (Bit 8)) #stCapVal;
          LET stArr <-
            fold_left (fun newArr i => newArr @[addr + $i <- ITE ($i < size)
                                                               (#stBytes@[$$(natToWord (Nat.log2_up NumBanks) i)])
                                                               (newArr@[addr + $i])])
              (seq 0 NumBanks) #memArr;
          WriteIf pred Then @^memArray: Array NumMemBytes (Bit 8) <- #stArr;
          WriteIf pred Then @^tagArray: Array NumMemBytes Bool <- #updTagPlus1;
          Retv ).
    End LoadStore.
  End ty.
End MemSpec.
