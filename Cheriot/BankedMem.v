Require Import Kami.AllNotations ProcKami.Cheriot.Lib ProcKami.Cheriot.Types.

Section BankedMem.
  Context `{procParams: ProcParams}.
  
  Local Ltac dischargeDiv8 :=
    unfold NumBanks, FullCap, Cap, CapSz, Data;
    let H := fresh in
    destruct (xlenIs32_or_64) as [H | H]; rewrite H; auto.
  
  Definition createRegFile (mb: MemBankParams) :=
    {|rfIsWrMask := false;
      rfNum := 1;
      rfDataArray := memArrayName mb;
      rfRead := Async [instRqName mb; loadRqName mb];
      rfWrite := storeRqName mb;
      rfIdxNum := NumMemBytes;
      rfData := Bit 8;
      rfInit := regFileInit mb |}.

  Definition memFiles := map createRegFile memBankInits.

  (* On normal stores (i.e. stores of data, not stores of caps),
     we may do two writes of false into consecutive tags;
     therefore we have two-way banked booleans for tagFile *)
  Definition tagFile (n : nat) :=
    {|rfIsWrMask := false;
      rfNum := 1;
      rfDataArray := (tagArray ++ natToBinStr n)%string;
      rfRead := Async [(tagRead ++ natToBinStr n)%string];
      rfWrite := (tagWrite ++ natToBinStr n)%string;
      rfIdxNum := NumMemBytes/2;
      rfData := Bool;
      rfInit := RFNonFile _ (Some (ConstBool false)) |}.

  Variable ty: Kind -> Type.
  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Section LoadInst.
    Variable addr: Addr @# ty.
    
    Section CommonIdx.
      Variable idx idxPlus1: Bit (Nat.log2_up NumMemBytes) @# ty.
      Variable idxLsb: Bit (Nat.log2_up NumBanks) @# ty.

      Local Fixpoint instReqCallHelp (mbs: list MemBankParams)
        (exprs: list (Bit 8 @# ty)) (pos: nat) : ActionT ty (Array (length exprs + length mbs) (Bit 8)). refine
        match mbs return ActionT ty (Array (length exprs + length mbs) (Bit 8)) with
        | [] => Ret (BuildArray (nth_Fin' exprs (@Nat.add_0_r _)))
        | m :: ms => ( LET actualIdx <- ITE ($pos < idxLsb) idxPlus1 idx;
                       LETA ret <- callReadRegFile (Bit 8) (instRqName m) #actualIdx;
                       (eq_rect _ _ (instReqCallHelp ms
                                       (exprs ++ [#ret]) (S pos)) _ _))
        end.
      abstract (rewrite app_length, <- Nat.add_assoc; reflexivity).
      Defined.
    End CommonIdx.

    Definition InstRet := STRUCT_TYPE {
                              "inst" :: Inst;
                              "badLower16?" :: Bool;
                              "error?" :: Bool;
                              "fault?" :: Bool;
                              "justFenceI?" :: Bool
                            }.
    
    Definition instReq: ActionT ty InstRet :=
      ( LET idx <- ZeroExtendTruncLsb (Nat.log2_up NumMemBytes) addr;
        LET idxPlus1 <- #idx + $1;
        LET idxLsb <- ZeroExtendTruncLsb (Nat.log2_up NumBanks) addr;
        LETA bytes <- instReqCallHelp #idx #idxPlus1 #idxLsb memBankInits [] 0;
        LET shuffledBytes <- ShuffleArray #bytes #idxLsb;
        Ret (STRUCT {
                 "inst" ::= (ZeroExtendTruncLsb InstSz (pack #shuffledBytes));
                 "badLower16?" ::= Const ty false;
                 "error?" ::= Const ty false;
                 "fault?" ::= Const ty false;
                 "justFenceI?" ::= Const ty false } : InstRet @# ty)).
  End LoadInst.

  Section LoadStore.
    Variable isStore: Bool @# ty.
    Variable addr: Addr @# ty.
    Variable size: MemSize @# ty.
    Variable isCap: Bool @# ty.
    Variable data: FullCapWithTag @# ty.
    Variable signed: Bool @# ty.

    Section CommonIdx.
      Variable idx idxPlus1: Bit (Nat.log2_up NumMemBytes) @# ty.
      Variable idxLsb: Bit (Nat.log2_up NumBanks) @# ty.
      Variable bytes: Array NumBanks (Bit 8) @# ty.

      Local Fixpoint memReqCallHelp (mbs: list MemBankParams) (pos: nat)
        (exprs: list (Bit 8 @# ty)) : ActionT ty (Array (length exprs + length mbs) (Bit 8)). refine
        match mbs with
        | [] => Ret (BuildArray (nth_Fin' exprs (@Nat.add_0_r _)))
        | m :: ms => ( LET inpPos <- $pos - idxLsb;
                       LET actualIdx <- ITE (unpack Bool (ZeroExtendTruncMsb 1 #inpPos)) idxPlus1 idx;
                       LET isWrite <- (ZeroExtend 1 #inpPos) < size;
                       If isStore
                       then ( If #isWrite
                              then callWriteRegFile (storeRqName m) #actualIdx (bytes @[ #inpPos ])
                              else Retv;
                              Ret (Const ty Default) )
                       else callReadRegFile (Bit 8) (loadRqName m) #actualIdx
                       as ret;
                       (eq_rect _ _ (memReqCallHelp ms (S pos) (exprs ++ [#ret])) _ _))
        end.
      abstract (rewrite app_length, <- Nat.add_assoc; reflexivity).
      Defined.
    End CommonIdx.

    Definition DataRet := STRUCT_TYPE {
                              "data" :: FullCapWithTag;
                              "lowestByte" :: Bit (Nat.log2_up NumBanks);
                              "dataError?" :: Bool;
                              "dataFault?" :: Bool;
                              "tagError?" :: Bool;
                              "tagFault?" :: Bool }.

    Definition loadStoreReq: ActionT ty DataRet.
      refine
        ( LET idx <- ZeroExtendTruncLsb (Nat.log2_up NumMemBytes) addr;
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
          LET straddle <- ZeroExtend 1 #idxLsb + size <= $NumBanks;
          LET tagIdx : Maybe _ <- Valid (ZeroExtendTruncMsb (Nat.log2_up (NumMemBytes/2)) #idx);
          LET tagIdxPlus1 : Maybe _ <- (STRUCT { "valid" ::= #straddle;
                                                 "data" ::= ZeroExtendTruncMsb (Nat.log2_up (NumMemBytes/2))
                                                              #idxPlus1}: Maybe _ @# ty);
          LET tagIdxLsbIs0 <- unpack Bool (ZeroExtendTruncLsb 1 #idx);
          LET tag0Idx <- ITE #tagIdxLsbIs0 #tagIdx #tagIdxPlus1;
          LET tag1Idx <- ITE #tagIdxLsbIs0 #tagIdxPlus1 #tagIdx;
          (* For stores, if isCap, then tagIdx is valid and tagIdxPlus1 is invalid,
             so only one of tag0Idx or tag1Idx is valid *)
          If isStore
          then ( If (#tag0Idx @% "valid")
                 then callWriteRegFile (tagWrite ++ "0")%string (#tag0Idx @% "data")
                        (ITE isCap (data @% "tag") $$false)
                 else Retv;
                 If (#tag1Idx @% "valid")
                 then callWriteRegFile (tagWrite ++ "1")%string (#tag1Idx @% "data")
                        (ITE isCap (data @% "tag") $$false)
                 else Retv;
                 Ret (Const ty Default) )
          else ( If isCap
                 then callReadRegFile Bool tagRead #idx
                 else Ret (Const ty Default)
                 as retTag;
                 Ret #retTag )
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
      - abstract (rewrite lengthMemBankInits; dischargeDiv8).
    Defined.
  End LoadStore.
End BankedMem.
