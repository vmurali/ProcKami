Require Import Kami.AllNotations ProcKami.Cheriot.Types.

Section BankedMem.
  Context `{procParams: ProcParams}.
  
  Variable Size: nat.
  Variable tagRead tagWrite tagDataArray: string.

  Record MemBankInit := {
      instName: string;
      loadName: string;
      storeName: string;
      dataArrayName: string;
      regFileInit: RegFileInitT Size (Bit 8) }.
  Variable memBankInits: list MemBankInit.
  Definition NumBanks := (CapSz + Xlen) / 8.
  Variable lengthMemBankInits: length memBankInits = NumBanks.

  Local Ltac dischargeDiv8 :=
    unfold NumBanks, FullCap, Cap, CapSz, Data;
    let H := fresh in
    destruct (xlenIs32_or_64) as [H | H]; rewrite H; auto.
  
  Local Ltac dischargeLengthMemBankInits :=
    rewrite lengthMemBankInits;
    dischargeDiv8.

  Definition createRegFile (mb: MemBankInit) :=
    {|rfIsWrMask := false;
      rfNum := 1;
      rfDataArray := dataArrayName mb;
      rfRead := Async [instName mb; loadName mb];
      rfWrite := storeName mb;
      rfIdxNum := Size;
      rfData := Bit 8;
      rfInit := regFileInit mb |}.

  Definition memFiles := map createRegFile memBankInits.

  Definition tagFile :=
    {|rfIsWrMask := false;
      rfNum := 1;
      rfDataArray := tagDataArray;
      rfRead := Async [tagRead];
      rfWrite := tagWrite;
      rfIdxNum := Size;
      rfData := Bool;
      rfInit := RFNonFile _ (Some (ConstBool false)) |}.

  Variable ty: Kind -> Type.
  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Section LoadInst.
    Variable addr: Addr @# ty.
    
    Section CommonIdx.
      Variable idx idxPlus1: Bit (Nat.log2_up Size) @# ty.
      Variable idxLsb: Bit (Nat.log2_up NumBanks) @# ty.

      Local Fixpoint instReqCallHelp (mbs: list MemBankInit)
        (exprs: list (Bit 8 @# ty)) (pos: nat) : ActionT ty (Array (length exprs + length mbs) (Bit 8)). refine
        match mbs return ActionT ty (Array (length exprs + length mbs) (Bit 8)) with
        | [] => Ret (BuildArray (nth_Fin' exprs (@Nat.add_0_r _)))
        | m :: ms => ( LET actualIdx <- ITE ($pos < idxLsb) idxPlus1 idx;
                       Call ret : Array 1 (Bit 8) <- (instName m) (#actualIdx : Bit (Nat.log2_up Size));
                       (eq_rect _ _ (instReqCallHelp ms
                                       (exprs ++ [ReadArrayConst #ret Fin.F1]) (S pos)) _ _))
        end.
      abstract (rewrite app_length, <- Nat.add_assoc; reflexivity).
      Defined.
    End CommonIdx.
    
    Definition instReq: ActionT ty FullCap.
      refine
        ( LET idx <- ZeroExtendTruncLsb (Nat.log2_up Size) addr;
          LET idxPlus1 <- #idx + $1;
          LET idxLsb <- ZeroExtendTruncLsb (Nat.log2_up NumBanks) addr;
          LETA bytes <- instReqCallHelp #idx #idxPlus1 #idxLsb memBankInits [] 0;
          LET shuffledBytes <- ShuffleArray #bytes #idxLsb;
          Ret (unpack FullCap (castBits _ (pack #shuffledBytes)) )).
      abstract dischargeLengthMemBankInits.
    Defined.
  End LoadInst.

  Section LoadStore.
    Variable isStore: Bool @# ty.
    Variable addr: Addr @# ty.
    Variable size: MemSize @# ty.
    Variable isCap: Bool @# ty.
    Variable data: FullCapWithTag @# ty.
    Variable signed: Bool @# ty.

    Section CommonIdx.
      Variable idx idxPlus1: Bit (Nat.log2_up Size) @# ty.
      Variable idxLsb: Bit (Nat.log2_up NumBanks) @# ty.
      Variable bytes: Array NumBanks (Bit 8) @# ty.

      Local Fixpoint memReqCallHelp (mbs: list MemBankInit) (pos: nat)
        (exprs: list (Bit 8 @# ty)) : ActionT ty (Array (length exprs + length mbs) (Bit 8)). refine
        match mbs with
        | [] => Ret (BuildArray (nth_Fin' exprs (@Nat.add_0_r _)))
        | m :: ms => ( LET inpPos <- $pos - idxLsb;
                       LET actualIdx <- ITE (unpack Bool (ZeroExtendTruncMsb 1 #inpPos)) idxPlus1 idx;
                       LET isWrite <- (ZeroExtend 1 #inpPos) < size;
                       LET writeRq <- STRUCT { "addr" ::= #actualIdx;
                                               "data" ::= BuildArray (fun _ => bytes @[ #inpPos ] ) };
                       If isStore
                       then ( If #isWrite
                              then Call (storeName m) (#writeRq : WriteRq (Nat.log2_up Size) (Array 1 (Bit 8))); Retv
                              else Retv;
                              Ret (Const ty Default) )
                       else ( Call ret : Array 1 (Bit 8) <- (loadName m) (#actualIdx : Bit (Nat.log2_up Size));
                              Ret #ret ) as retVal;
                       (eq_rect _ _ (memReqCallHelp ms (S pos) (exprs ++ [ReadArrayConst #retVal Fin.F1])) _ _))
        end.
      abstract (rewrite app_length, <- Nat.add_assoc; reflexivity).
      Defined.
    End CommonIdx.

    Definition loadStoreReq: ActionT ty FullCapWithTag.
      refine
        ( LET idx <- ZeroExtendTruncLsb (Nat.log2_up Size) addr;
          LET idxPlus1 <- #idx + $1;
          LET idxLsb <- ZeroExtendTruncLsb (Nat.log2_up NumBanks) addr;
          LET capVal <- {< (data @% "cap"), (data @% "val") >};
          LET bytes <- unpack (Array NumBanks (Bit 8)) (castBits _ #capVal);
          LETA ldBytes <- memReqCallHelp #idx #idxPlus1 #idxLsb #bytes memBankInits 0 [];
          LET shuffledLdBytes <- ShuffleArray #ldBytes #idxLsb;
          LET ldSignVal <- (IF signed
                            then TruncToDynamicSizeArraySigned #shuffledLdBytes size
                            else TruncToDynamicSizeArrayUnsigned #shuffledLdBytes size);
          LET ldVal <- unpack FullCap (castBits _ (pack #ldSignVal));
          LET tagWriteRq <- STRUCT { "addr" ::= #idx;
                                     "data" ::= BuildArray (fun _ => data @% "tag") };
          If isStore
          then ( If isCap
                 then Call tagWrite (#tagWriteRq: WriteRq (Nat.log2_up Size) (Array 1 Bool)); Retv
                 else Retv;
                 Ret (Const ty Default) )
          else ( Call tag: Array 1 Bool <- tagRead (#idx : Bit (Nat.log2_up Size)); Ret (#tag ![ 0 ]) )
          as tag;
          Ret (STRUCT {
                   "tag" ::= #tag;
                   "cap" ::= #ldVal @% "cap";
                   "val" ::= #ldVal @% "val" } : FullCapWithTag @# ty) ).
      - abstract dischargeDiv8.
      - abstract dischargeLengthMemBankInits.
    Defined.
  End LoadStore.
End BankedMem.
