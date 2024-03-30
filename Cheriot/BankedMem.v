Require Import Kami.AllNotations ProcKami.Cheriot.Lib ProcKami.Cheriot.Types.
  
Section BankedMem.
  Variable procName: string.
  Context `{memParams: MemParams}.
  Local Notation "@^ x" := (procName ++ "_" ++ x)%string (at level 0).

  Definition InstRet := STRUCT_TYPE {
                            "inst" :: Inst;
                            "badLower16?" :: Bool;
                            "error?" :: Bool;
                            "fault?" :: Bool;
                            "justFenceI?" :: Bool }.

  Definition DataRet := STRUCT_TYPE {
                            "data" :: FullCapWithTag;
                            "lowestByte" :: Bit (Nat.log2_up NumBanks);
                            "dataError?" :: Bool;
                            "dataFault?" :: Bool;
                            "tagError?" :: Bool;
                            "tagFault?" :: Bool }.

  Definition createRegFile (mb: Fin.t NumBanks * MemBankInit) :=
    {|rfIsWrMask := false;
      rfNum := 1;
      rfDataArray := @^(memArrayName (snd mb));
      rfRead := Async [@^(instRqName (snd mb)); @^(loadRqName (snd mb))];
      rfWrite := @^(storeRqName (snd mb));
      rfIdxNum := NumMemBytes;
      rfData := Bit 8;
      rfInit := RFFile isMemAscii isMemRfArg (memRfString (snd mb)) 0 NumMemBytes
                  (fun i => memInit (Fin.depair i (fst mb))) |}.

  Definition memFiles := map createRegFile
                           (match lengthMemBankInits in _ = Y return list (Fin.t Y * MemBankInit) with
                            | eq_refl => finTag memBankInits
                            end).

  (* On normal stores (i.e. stores of data, not stores of caps),
     we may do two writes of false into consecutive tags;
     therefore we have two-way banked booleans for tagFile *)
  Definition tagFile (n : nat) :=
    {|rfIsWrMask := false;
      rfNum := 1;
      rfDataArray := (@^tagArray ++ natToBinStr n)%string;
      rfRead := Async [(@^tagRead ++ natToBinStr n)%string];
      rfWrite := (@^tagWrite ++ natToBinStr n)%string;
      rfIdxNum := NumMemBytes/2;
      rfData := Bool;
      rfInit := RFNonFile _ (Some (ConstBool false)) |}.

  Section ty.
    Variable ty: Kind -> Type.
    Local Open Scope kami_expr.
    Local Open Scope kami_action.

    Section LoadInst.
      Variable addr: Addr @# ty.
      
      Section CommonIdx.
        Variable idx idxPlus1: Bit (Nat.log2_up NumMemBytes) @# ty.
        Variable idxLsb: Bit (Nat.log2_up NumBanks) @# ty.

        Local Fixpoint instReqCallHelp (mbs: list MemBankInit)
          (exprs: list (Bit 8 @# ty)) (pos: nat) : ActionT ty (Array (length exprs + length mbs) (Bit 8)). refine
          match mbs return ActionT ty (Array (length exprs + length mbs) (Bit 8)) with
          | [] => Ret (BuildArray (nth_Fin' exprs (@Nat.add_0_r _)))
          | m :: ms => ( LET actualIdx <- ITE ($pos < idxLsb) idxPlus1 idx;
                         LETA ret <- callReadRegFile (Bit 8) (@^(instRqName m)) #actualIdx;
                         (eq_rect _ _ (instReqCallHelp ms
                                         (exprs ++ [#ret]) (S pos)) _ _))
          end.
        abstract (rewrite app_length, <- Nat.add_assoc; reflexivity).
        Defined.
      End CommonIdx.

      Definition instReq: ActionT ty InstRet :=
        ( LET idx <- ZeroExtendTruncLsb (Nat.log2_up NumMemBytes)
                       (TruncMsbTo (Xlen - Nat.log2_up NumBanks) (Nat.log2_up NumBanks) addr);
          LET idxPlus1 <- #idx + $1;
          LET idxLsb <- TruncLsbTo (Nat.log2_up NumBanks) _ addr;
          LETA bytes <- instReqCallHelp #idx #idxPlus1 #idxLsb memBankInits [] 0;
          LET shuffledBytes <- ShuffleArray #bytes #idxLsb;
          Read justFenceI : Bool <- justFenceIReg;
          Write justFenceIReg : Bool <- $$false;
          Ret (STRUCT {
                   "inst" ::= (TruncLsbTo InstSz _ (pack #shuffledBytes));
                   "badLower16?" ::= Const ty false;
                   "error?" ::= Const ty false;
                   "fault?" ::= Const ty false;
                   "justFenceI?" ::= #justFenceI } : InstRet @# ty)).

    End LoadInst.

    Section LoadStore.
      Variable addr: Addr @# ty.
      Variable size: MemSize @# ty.
      Variable isCap: Bool @# ty.
      Variable signed: Bool @# ty.
      Variable isStore: Bool @# ty.
      Variable data: FullCapWithTag @# ty.

      Section CommonIdx.
        Variable idx idxPlus1: Bit LgNumMemBytes @# ty.
        Variable idxLsb: Bit (Nat.log2_up NumBanks) @# ty.
        Variable bytes: Array NumBanks (Bit 8) @# ty.

        Local Fixpoint memReqCallHelp (mbs: list MemBankInit) (pos: nat)
          (exprs: list (Bit 8 @# ty)) : ActionT ty (Array (length exprs + length mbs) (Bit 8)). refine
          match mbs return ActionT ty (Array (length exprs + length mbs) (Bit 8))with
          | [] => Ret (BuildArray (nth_Fin' exprs (@Nat.add_0_r _)))
          | m :: ms => ( LET inpPos <- $pos - idxLsb;
                         LET actualIdx <- ITE (unpack Bool (TruncMsbTo 1 (pred (Nat.log2_up NumBanks)) #inpPos))
                                            idxPlus1
                                            idx;
                         LET isWrite <- (ZeroExtend 1 #inpPos) < size;
                         If isStore
                         then ( If #isWrite
                                then callWriteRegFile (@^(storeRqName m)) #actualIdx (bytes @[ #inpPos ])
                                else Retv;
                                Ret (Const ty Default) )
                         else callReadRegFile (Bit 8) (@^(loadRqName m)) #actualIdx
                         as ret;
                         (eq_rect _ _ (memReqCallHelp ms (S pos) (exprs ++ [#ret])) _ _))
          end.
        abstract (rewrite app_length, <- Nat.add_assoc; reflexivity).
        Defined.
      End CommonIdx.

      Local Ltac dischargeDiv8 :=
        unfold NumBanks, FullCap, Cap, CapSz, Data; auto.

      Definition loadStoreReq: ActionT ty DataRet :=
        ( LET idx <- ZeroExtendTruncLsb LgNumMemBytes
                       (TruncMsbTo (Xlen - Nat.log2_up NumBanks) (Nat.log2_up NumBanks) addr);
          LET idxPlus1 <- #idx + $1;
          LET idxLsb <- TruncLsbTo (Nat.log2_up NumBanks) _ addr;
          LET capVal <- {< pack (data @% "cap"), (data @% "val") >};
          LET bytes <- unpack (Array NumBanks (Bit 8)) #capVal;
          LETA ldBytes <- memReqCallHelp #idx #idxPlus1 #idxLsb #bytes memBankInits 0 [];
          LET shuffledLdBytes <- ShuffleArray #ldBytes #idxLsb;
          LET ldSignVal <- (IF signed
                            then TruncToDynamicSizeArraySigned #shuffledLdBytes size
                            else TruncToDynamicSizeArrayUnsigned #shuffledLdBytes size);
          LET ldVal <- unpack FullCap (pack #ldSignVal);
          LET straddle <- ZeroExtend 1 #idxLsb + size <= $NumBanks;
          LET tagIdxBaseMsb <- ZeroExtendTruncMsb (LgNumMemBytes-1) #idx;
          LET tagIdx : Maybe _ <- Valid #tagIdxBaseMsb;
          LET tagIdxPlus1 : Maybe _ <- (STRUCT { "valid" ::= #straddle;
                                                 "data" ::= (#tagIdxBaseMsb + $1)}: Maybe _ @# ty);
          LET tagIdxLsbIs0 <- unpack Bool (ZeroExtendTruncLsb 1 #idx);
          LET tag0Idx <- ITE #tagIdxLsbIs0 #tagIdx #tagIdxPlus1;
          LET tag1Idx <- ITE #tagIdxLsbIs0 #tagIdxPlus1 #tagIdx;
          (* For stores, if isCap, then tagIdx is valid and tagIdxPlus1 is invalid,
             so only one of tag0Idx or tag1Idx is valid *)
          If isStore
          then ( If (#tag0Idx @% "valid")
                 then callWriteRegFile (@^tagWrite ++ "0")%string (#tag0Idx @% "data")
                        (ITE isCap (data @% "tag") $$false)
                 else Retv;
                 If (#tag1Idx @% "valid")
                 then callWriteRegFile (@^tagWrite ++ "1")%string (#tag1Idx @% "data")
                        (ITE isCap (data @% "tag") $$false)
                 else Retv;
                 Ret (Const ty Default) )
          else ( If isCap
                 then callReadRegFile Bool @^tagRead #idx
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
    End LoadStore.
  End ty.
End BankedMem.
