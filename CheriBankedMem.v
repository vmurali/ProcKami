Require Import Kami.AllNotations ProcKami.CheriTypes ProcKami.Lib.

Section BankedMem.
  Context `{procParams: ProcParams}.
  
  Variable Size: nat.
  Record MemBankInit := {
      instName: string;
      loadName: string;
      storeName: string;
      dataArrayName: string;
      regFileInit: RegFileInitT Size (Bit 8) }.

  Variable memBankInits: list MemBankInit.
  Variable tagRead tagWrite tagDataArray: string.
  Variable numMemBankInits: length memBankInits = (CapSz + Xlen) / 8.

  Ltac dischargeNumBanksLengthMemBankInits :=
    rewrite numMemBankInits;
    unfold FullCap, Cap, CapSz, Data;
    destruct (xlenIs32_or_64) as [H | H]; rewrite H; auto.
  
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

  Section Load.
    Variable addr: Addr @# ty.
    Variable isInst: bool.
    
    Section CommonIdx.
      Variable idx idxPlus1: Bit (Nat.log2_up Size) @# ty.
      Variable idxLsb: Bit (Nat.log2_up (length memBankInits)) @# ty.

      Local Fixpoint loadReqBytesCallHelp (mbs: list MemBankInit)
        (exprs: list (Bit 8 @# ty)) (pos: nat) : ActionT ty (Array (length exprs + length mbs) (Bit 8)). refine
        match mbs return ActionT ty (Array (length exprs + length mbs) (Bit 8)) with
        | [] => Ret (BuildArray (nth_Fin' exprs (@Nat.add_0_r _)))
        | m :: ms => ( LET actualIdx <- ITE ($pos < idxLsb) idxPlus1 idx;
                       Call ret : Array 1 (Bit 8) <- ((if isInst then instName else loadName) m) (#actualIdx : Bit (Nat.log2_up Size));
                       (eq_rect _ _ (loadReqBytesCallHelp ms (exprs ++ [ReadArrayConst #ret Fin.F1]) (S pos)) _ _))
        end.
      abstract (rewrite app_length;
                rewrite <- Nat.add_assoc;
                reflexivity).
      Defined.
    End CommonIdx.
    
    Definition loadReq: ActionT ty FullCapWithTag.
      refine
        ( LET idx <- ZeroExtendTruncLsb (Nat.log2_up Size) addr;
          LET idxPlus1 <- #idx + $1;
          LET idxLsb <- ZeroExtendTruncLsb (Nat.log2_up (length memBankInits)) addr;
          LETA bytes <- loadReqBytesCallHelp #idx #idxPlus1 #idxLsb memBankInits [] 0;
          LET shuffledBytes <- ShuffleArray #bytes #idxLsb;
          LET unpacked <- unpack FullCap (castBits _ (pack #shuffledBytes));
          Call tag : Bool <- tagRead (#idx: Bit (Nat.log2_up Size));
          Ret (STRUCT {
                   "tag" ::= #tag;
                   "cap" ::= #unpacked @% "cap";
                   "val" ::= #unpacked @% "val" } : FullCapWithTag @# ty)).
      abstract dischargeNumBanksLengthMemBankInits.
    Defined.
  End Load.

  Section Store.
    Variable addr: Addr @# ty.
    Variable size: MemSize @# ty.
    Variable isCap: Bool @# ty.
    Variable data: FullCapWithTag @# ty.

    Section CommonIdx.
      Variable idx idxPlus1: Bit (Nat.log2_up Size) @# ty.
      Variable idxLsb: Bit (Nat.log2_up (length memBankInits)) @# ty.
      Variable bytes: Array (length memBankInits) (Bit 8) @# ty.

      Local Fixpoint storeReqBytesCallHelp (mbs: list MemBankInit) (pos: nat) : ActionT ty Void. refine
        match mbs with
        | [] => Retv
        | m :: ms => ( LET inpPos <- $pos - idxLsb;
                       LET actualIdx <- ITE (unpack Bool (ZeroExtendTruncMsb 1 #inpPos)) idxPlus1 idx;
                       LET isWrite <- (ZeroExtend 1 #inpPos) < castBits _ size;
                       LET writeRq <- STRUCT { "addr" ::= #actualIdx;
                                               "data" ::= BuildArray (fun _ => bytes @[ #inpPos ] ) };
                       If #isWrite
                       then Call (storeName m) (#writeRq : WriteRq (Nat.log2_up Size) (Array 1 (Bit 8))); Retv
                       else Retv;
                       storeReqBytesCallHelp ms (S pos) )
        end.
      abstract (rewrite numMemBankInits; auto).
      Defined.
    End CommonIdx.

    Definition storeReq: ActionT ty Void.
      refine
        ( LET idx <- ZeroExtendTruncLsb (Nat.log2_up Size) addr;
          LET idxPlus1 <- #idx + $1;
          LET idxLsb <- ZeroExtendTruncLsb (Nat.log2_up (length memBankInits)) addr;
          LET capVal <- {< (data @% "cap"), (data @% "val") >};
          LET bytes <- unpack (Array (length memBankInits) (Bit 8)) (castBits _ #capVal);
          LETA _ <- storeReqBytesCallHelp #idx #idxPlus1 #idxLsb #bytes memBankInits 0;
          LET tagWriteRq <- STRUCT { "addr" ::= #idx;
                                     "data" ::= BuildArray (fun _ => data @% "tag") };
          If isCap
          then Call tagWrite (#tagWriteRq: WriteRq (Nat.log2_up Size) (Array 1 Bool)); Retv
          else Retv;
          Retv ).
      abstract dischargeNumBanksLengthMemBankInits.
    Defined.
  End Store.
End BankedMem.
