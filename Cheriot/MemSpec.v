Require Import Kami.AllNotations ProcKami.Cheriot.Lib ProcKami.Cheriot.Types ProcKami.Cheriot.MemSpecIfc.

Section MemSpec.
  Context `{procParams: ProcParams}.
  
  Local Ltac dischargeDiv8 :=
    unfold NumBanks, FullCap, Cap, CapSz, Data;
    let H := fresh in
    destruct (xlenIs32_or_64) as [H | H]; rewrite H; auto.
  
  Section ty.
    Variable ty: Kind -> Type.
    Local Open Scope kami_expr.
    Local Open Scope kami_action.

    Section LoadInst.
      Variable addr: Addr @# ty.

      Section ReadArray.
        Variable n: nat.
        Variable arr: Array n (Bit 8) @# ty.
        Definition readArrayConstSize (size: nat) :=
          BuildArray (fun (i: Fin.t size) => arr@[addr + $(FinFun.Fin2Restrict.f2n i)]).
      End ReadArray.

      Definition instReqImpl: ActionT ty InstRet :=
        ( Read justFenceI : Bool <- justFenceIReg;
          Write justFenceIReg : Bool <- $$false;
          Read memArr: Array NumMemBytes (Bit 8) <- memArray;
          Ret (STRUCT {
                   "inst" ::= pack (readArrayConstSize #memArr 4);
                   "badLower16?" ::= Const ty false;
                   "error?" ::= Const ty false;
                   "fault?" ::= Const ty false;
                   "justFenceI?" ::= #justFenceI } : InstRet @# ty)).
    End LoadInst.

    Section LoadStore.
      Variable isStore: Bool @# ty.
      Variable addr: Addr @# ty.
      Variable size: MemSize @# ty.
      Variable isCap: Bool @# ty.
      Variable data: FullCapWithTag @# ty.
      Variable signed: Bool @# ty.

      Theorem NumBanksNotZero: NumBanks = S (NumBanks - 1).
      Proof.
        unfold NumBanks.
        unfold Xlen, CapSz, Xlen.
        destruct procParams.
        destruct xlenIs32_or_64; subst; auto.
      Qed.

      Definition loadStoreReqImpl: ActionT ty DataRet.
        refine
          ( LET idx <- ZeroExtendTruncLsb (Nat.log2_up NumMemBytes) addr;
            LET idxLsb <- ZeroExtendTruncLsb (Nat.log2_up NumBanks) addr;
            LET capVal <- {< (data @% "cap"), (data @% "val") >};
            LET bytes <- unpack (Array NumBanks (Bit 8)) (castBits _ #capVal);
            Read memArr : Array NumMemBytes (Bit 8) <- memArray;
            LET ldBytes <- readArrayConstSize addr #memArr NumBanks;
            LET ldSignVal <- (IF signed
                              then TruncToDynamicSizeArraySigned #ldBytes size
                              else TruncToDynamicSizeArrayUnsigned #ldBytes size);
            LET ldVal <- unpack FullCap (castBits _ (pack #ldSignVal));
            LET straddle <- ZeroExtend 1 #idxLsb + size <= $NumBanks;
            LET tagIdx <- ZeroExtendTruncMsb LgNumTags #idx;
            Read tags: Array NumTags Bool <- tagArray;
            LET tagVal <- #tags@[#tagIdx];
            LET updTag <- #tags@[ #tagIdx <- ITE isCap (data @% "tag") $$false];
            LET updTagPlus1 <- ITE #straddle (#updTag@[ #tagIdx + $1 <- ITE isCap #tagVal $$false]) #updTag;
            LET stArr <-
              fold_left (fun newArr i =>
                           newArr @[addr + $i <-
                                      ITE ($i < size)
                                        (match NumBanksNotZero in _ = Y return Array Y (Bit 8) @# ty with
                                         | eq_refl => #bytes
                                         end![i]) (#memArr@[addr + $i])])
                (seq 0 NumBanks) #memArr;
            If isStore
            then ( Write memArray: Array NumMemBytes (Bit 8) <- #stArr;
                   Write tagArray: Array NumTags Bool <- #updTagPlus1;
                   Ret (Const ty Default) )
            else ( Ret (ITE isCap #tagVal (Const ty Default)) )
            as tag;
            Ret (STRUCT {
                     "data" ::= (STRUCT {
                                     "tag" ::= #tag;
                                     "cap" ::= #ldVal @% "cap";
                                     "val" ::= #ldVal @% "val" } : FullCapWithTag @# ty);
                     "lowestByte" ::= $0;
                     "dataError?" ::= Const ty false;
                     "dataFault?" ::= Const ty false;
                     "tagError?" ::= Const ty false;
                     "tagFault?" ::= Const ty false } : DataRet @# ty) ).
        - abstract dischargeDiv8.
        - abstract dischargeDiv8.
      Defined.
    End LoadStore.
  End ty.
    
  Instance memSpec: MemSpecIfc :=
    {|instReq := instReqImpl;
      loadStoreReq := loadStoreReqImpl |}.
End MemSpec.
