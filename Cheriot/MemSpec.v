Require Import Kami.AllNotations ProcKami.Cheriot.Lib ProcKami.Cheriot.Types.

Section MemSpec.
  Variable procName: string.
  Context `{memParams: MemParams}.
  
  Section ty.
    Variable ty: Kind -> Type.
    Local Open Scope kami_expr.
    Local Open Scope kami_action.

    Local Notation "@^ x" := ((procName ++ "_") ++ x)%string (at level 0).

    Section Inst.
      Variable addr: Addr @# ty.

      Definition instReqSpec: ActionT ty Inst :=
        ( Read memArr: Array NumMemBytes FullCapWithTag <- @^memArray;
          LET instFullCap <- rmTag (#memArr@[ TruncMsbTo (AddrSz - LgNumBanks) LgNumBanks addr]);
          LET isUpper <- unpack Bool
                           (TruncMsbTo 1 (LgNumBanks - 1) (TruncLsbTo LgNumBanks (AddrSz - LgNumBanks) addr));
          Ret (ITE #isUpper (pack (#instFullCap @% "cap")) (#instFullCap @% "val")) ).
    End Inst.

    Section LoadStore.
      Variable pred: Bool @# ty.
      Variable addr: Addr @# ty.
      Variable size: MemSize @# ty.
      Variable isCap: Bool @# ty.
      Variable signed: Bool @# ty.
      Variable data: FullCapWithTag @# ty.
      
      Definition loadReqSpec: ActionT ty FullCapWithTag :=
        ( Read memArr: Array NumMemBytes FullCapWithTag <- @^memArray;
          LET rowIdx <- TruncMsbTo (AddrSz - LgNumBanks) LgNumBanks addr;
          LET row0: FullCapWithTag <- #memArr@[#rowIdx];
          LET row1: FullCapWithTag <- #memArr@[#rowIdx + $1];
          LET packedRows: Bit (Syntax.size (Array (2*NumBanks) (Bit 8))) <-
                            ({< pack (rmTag #row0), pack (rmTag #row1) >});
          LET twoRowBytes <- unpack (Array (2*NumBanks) (Bit 8)) #packedRows;
          LET offset <- TruncLsbTo LgNumBanks (AddrSz - LgNumBanks) addr;
          LET ldBytes <- readArrayConstSize #offset #twoRowBytes NumBanks;
          LET ldSignVal <- (IF signed
                            then TruncToDynamicSizeArraySigned #ldBytes size
                            else TruncToDynamicSizeArrayUnsigned #ldBytes size);
          LET retVal <- (IF isCap
                         then #row0
                         else (STRUCT { "tag" ::= $$false;
                                        "cap" ::= Const ty (getDefaultConst Cap);
                                        "val" ::= TruncLsbTo Xlen Xlen (pack #ldSignVal) }));
          Ret #retVal ).

      Definition storeReqSpec: ActionT ty Void :=
        ( Read memArr: Array NumMemBytes FullCapWithTag <- @^memArray;
          LET rowIdx <- TruncMsbTo (AddrSz - LgNumBanks) LgNumBanks addr;
          LET row0: FullCapWithTag <- #memArr@[#rowIdx];
          LET row1: FullCapWithTag <- #memArr@[#rowIdx + $1];
          LET packedRows: Bit (Syntax.size (Array (2*NumBanks) (Bit 8))) <-
                            ({< pack (rmTag #row0), pack (rmTag #row1) >});
          LET twoRowBytes <- unpack (Array (2*NumBanks) (Bit 8)) #packedRows;
          LET idxLsb <- TruncLsbTo LgNumBanks _ addr;
          LET straddle <- ZeroExtend 1 #idxLsb + size > $NumBanks;
          (* #straddle implies !#isCap *)
          LET updTagPlus1 <- ITE #straddle $$false (#row1 @% "tag");
          LET stCapVal <- {< pack (data @% "cap"), (data @% "val") >};
          LET stBytes <- unpack (Array NumBanks (Bit 8)) #stCapVal;
          LET offset <- TruncLsbTo LgNumBanks (AddrSz - LgNumBanks) addr;          
          LET stRows <-
            fold_left (fun newArr i => newArr @[#offset + $i <- ITE ($i < size)
                                                                  (#stBytes@[$$(natToWord LgNumBanks i)])
                                                                  (newArr@[#offset + $i])])
              (seq 0 NumBanks) #twoRowBytes;
          LET stRowsFullCap <- unpack (Pair FullCap FullCap) (pack #stRows);
          LET stRow0 <- STRUCT { "tag" ::= $$false;
                                 "cap" ::= #stRowsFullCap @% "fst" @% "cap";
                                 "val" ::= #stRowsFullCap @% "fst" @% "val" };
          LET stRow1 <- STRUCT { "tag" ::= #updTagPlus1;
                                 "cap" ::= #stRowsFullCap @% "snd" @% "cap";
                                 "val" ::= #stRowsFullCap @% "snd" @% "val" };
          WriteIf pred Then @^memArray: Array NumMemBytes FullCapWithTag <-
                                          (IF isCap
                                           then #memArr@[#rowIdx <- data]
                                           else #memArr@[#rowIdx <- #stRow0]@[#rowIdx + $1 <- #stRow1]);
          Retv ).
    End LoadStore.
  End ty.
End MemSpec.
