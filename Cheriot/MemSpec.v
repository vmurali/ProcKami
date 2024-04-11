Require Import Kami.AllNotations ProcKami.Cheriot.Lib ProcKami.Cheriot.Types.

Section MemSpec.
  Context `{memParams: MemParams}.
  
  Section ty.
    Variable ty: Kind -> Type.
    Local Open Scope kami_expr.
    Local Open Scope kami_action.

    Variable memArr: Array NumMemBytes FullCapWithTag @# ty.
    Section Inst.
      Variable addr: Addr @# ty.

      Definition instReqSpec: Inst ## ty :=
        ( LETC instFullCap <- rmTag (memArr@[ TruncMsbTo (AddrSz - LgNumBanks) LgNumBanks addr]);
          LETC isUpper <- unpack Bool
                            (TruncMsbTo 1 (LgNumBanks - 1) (TruncLsbTo LgNumBanks (AddrSz - LgNumBanks) addr));
          RetE (ITE #isUpper (pack (#instFullCap @% "cap")) (#instFullCap @% "val")) ).
    End Inst.

    Section LoadStore.
      Variable pred: Bool @# ty.
      Variable addr: Addr @# ty.
      Variable size: MemSize @# ty.
      Variable isCap: Bool @# ty.
      Variable signed: Bool @# ty.
      Variable data: FullCapWithTag @# ty.
      
      Definition loadReqSpec: FullCapWithTag ## ty :=
        ( LETC rowIdx <- TruncMsbTo (AddrSz - LgNumBanks) LgNumBanks addr;
          LETC row0: FullCapWithTag <- memArr@[#rowIdx];
          LETC row1: FullCapWithTag <- memArr@[#rowIdx + $1];
          LETC packedRows: Bit (Syntax.size (Array (2*NumBanks) (Bit 8))) <-
                             ({< pack (rmTag #row0), pack (rmTag #row1) >});
          LETC twoRowBytes <- unpack (Array (2*NumBanks) (Bit 8)) #packedRows;
          LETC offset <- TruncLsbTo LgNumBanks (AddrSz - LgNumBanks) addr;
          LETC ldBytes <- readArrayConstSize #offset #twoRowBytes NumBanks;
          LETC ldSignVal <- (IF signed
                             then TruncToDynamicSizeArraySigned #ldBytes size
                             else TruncToDynamicSizeArrayUnsigned #ldBytes size);
          LETC retVal <- (IF isCap
                          then #row0
                          else (STRUCT { "tag" ::= $$false;
                                         "cap" ::= Const ty (getDefaultConst Cap);
                                         "val" ::= TruncLsbTo Xlen Xlen (pack #ldSignVal) }));
          RetE #retVal ).

      Definition storeReqSpec: Array NumMemBytes FullCapWithTag ## ty :=
        ( LETC rowIdx <- TruncMsbTo (AddrSz - LgNumBanks) LgNumBanks addr;
          LETC row0: FullCapWithTag <- memArr@[#rowIdx];
          LETC row1: FullCapWithTag <- memArr@[#rowIdx + $1];
          LETC packedRows: Bit (Syntax.size (Array (2*NumBanks) (Bit 8))) <-
                             ({< pack (rmTag #row0), pack (rmTag #row1) >});
          LETC twoRowBytes <- unpack (Array (2*NumBanks) (Bit 8)) #packedRows;
          LETC idxLsb <- TruncLsbTo LgNumBanks _ addr;
          LETC straddle <- ZeroExtend 1 #idxLsb + size > $NumBanks;
          (* #straddle implies !#isCap *)
          LETC updTagPlus1 <- ITE #straddle $$false (#row1 @% "tag");
          LETC stCapVal <- {< pack (data @% "cap"), (data @% "val") >};
          LETC stBytes <- unpack (Array NumBanks (Bit 8)) #stCapVal;
          LETC offset <- TruncLsbTo LgNumBanks (AddrSz - LgNumBanks) addr;          
          LETC stRows <-
            fold_left (fun newArr i => newArr @[#offset + $i <- ITE ($i < size)
                                                                  (#stBytes@[$$(natToWord LgNumBanks i)])
                                                                  (newArr@[#offset + $i])])
              (seq 0 NumBanks) #twoRowBytes;
          LETC stRowsFullCap <- unpack (Pair FullCap FullCap) (pack #stRows);
          LETC stRow0 <- STRUCT { "tag" ::= $$false;
                                  "cap" ::= #stRowsFullCap @% "fst" @% "cap";
                                  "val" ::= #stRowsFullCap @% "fst" @% "val" };
          LETC stRow1 <- STRUCT { "tag" ::= #updTagPlus1;
                                  "cap" ::= #stRowsFullCap @% "snd" @% "cap";
                                  "val" ::= #stRowsFullCap @% "snd" @% "val" };
          RetE (IF pred
                then (IF isCap
                      then memArr@[#rowIdx <- data]
                      else memArr@[#rowIdx <- #stRow0]@[#rowIdx + $1 <- #stRow1])
                else memArr)).
    End LoadStore.
  End ty.
End MemSpec.
