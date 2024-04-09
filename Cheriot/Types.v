Require Import Kami.AllNotations ProcKami.Cheriot.Lib.
Require Import RecordUpdate.RecordUpdate.
Require Export ProcKami.Cheriot.CheriotTypes.

Section Roots.
  Section Ty.
    Variable ty: Kind -> Type.
    Local Open Scope kami_expr.
    Definition RootT := Z.pow 2 (Z.of_nat (CapBTSz - 1)).
    Definition ExecRootPermExpr : CapPerms @# ty := (Const ty (getDefaultConst CapPerms))
                                                      @%[ "GL" <- $$true ]
                                                      @%[ "EX" <- $$true ]
                                                      @%[ "LD" <- $$true ]
                                                      @%[ "MC" <- $$true ]
                                                      @%[ "LG" <- $$true ]
                                                      @%[ "LM" <- $$true ]
                                                      @%[ "SR" <- $$true ].

    Definition DataRootPermExpr : CapPerms @# ty := (Const ty (getDefaultConst CapPerms))
                                                      @%[ "GL" <- $$true ]
                                                      @%[ "LD" <- $$true ]
                                                      @%[ "SD" <- $$true ]
                                                      @%[ "MC" <- $$true ]
                                                      @%[ "SL" <- $$true ]
                                                      @%[ "LG" <- $$true ]
                                                      @%[ "LM" <- $$true ].

    Definition SealRootPermExpr : CapPerms @# ty := (Const ty (getDefaultConst CapPerms))
                                                      @%[ "GL" <- $$true ]
                                                      @%[ "SE" <- $$true ]
                                                      @%[ "US" <- $$true ]
                                                      @%[ "U0" <- $$true ].

    Definition ExecRootCapExpr: Cap @# ty := STRUCT { "R" ::= $0;
                                                      "p" ::= encodePerms ExecRootPermExpr;
                                                      "oType" ::= $0;
                                                      "E" ::= $$(wones CapESz);
                                                      "T" ::= $$(ZToWord CapBTSz RootT);
                                                      "B" ::= $0 }.
 
    Definition DataRootCapExpr: Cap @# ty := ExecRootCapExpr @%[ "p" <- encodePerms DataRootPermExpr ].
    Definition SealRootCapExpr: Cap @# ty := ExecRootCapExpr @%[ "p" <- encodePerms SealRootPermExpr ].
  End Ty.

  Definition ExecRootPerm : type (Bit CapPermSz) := evalExpr (encodePerms (ExecRootPermExpr _)).
  Definition DataRootPerm : type (Bit CapPermSz) := evalExpr (encodePerms (DataRootPermExpr _)).
  Definition SealRootPerm : type (Bit CapPermSz) := evalExpr (encodePerms (SealRootPermExpr _)).
  Definition ExecRootCap : type Cap := evalExpr (ExecRootCapExpr _).
  Definition DataRootCap : type Cap := evalExpr (DataRootCapExpr _).
  Definition SealRootCap : type Cap := evalExpr (SealRootCapExpr _).
End Roots.

Definition rmTag ty (cap: FullCapWithTag @# ty) : FullCap @# ty :=
  (STRUCT { "cap" ::= cap @% "cap"; "val" ::= cap @% "val" })%kami_expr.

Definition PccValid (pcCap: type Cap) :=
  evalLetExpr ( LETC perms <- getCapPerms ###pcCap;
                RetE (###perms @% "EX" && !(isCapSealed ###pcCap)))%kami_expr = true.

Theorem Extension_eq_dec: forall (e1 e2: Extension), {e1 = e2} + {e1 <> e2}.
Proof.
  decide equality.
Qed.

Definition Extension_eqb (e1 e2: Extension) : bool :=
  match e1, e2 with
  | Base, Base => true
  | M, M => true
  | _, _ => false
  end.

Theorem Extension_eqb_eq: forall e1 e2: Extension, (Extension_eqb e1 e2) = true <-> e1 = e2.
Proof.
  destruct e1, e2; constructor; discriminate || tauto.
Qed.

Theorem Extension_eqb_neq: forall e1 e2: Extension, (Extension_eqb e1 e2) = false <-> e1 <> e2.
Proof.
  destruct e1, e2; constructor; discriminate || tauto.
Qed.

Definition Inst := Bit InstSz.
Definition CompInst := Bit CompInstSz.
Definition RegId := Bit RegIdSz.
Definition ScrId := Bit ScrIdSz.

Definition isInstNotCompressed ty sz (bitString : Bit sz @# ty) := isNotZero (ZeroExtendTruncLsb 2 bitString).

Definition isInstCompressed ty sz (bitString : Bit sz @# ty) := isZero (ZeroExtendTruncLsb 2 bitString).

Definition MeieInit := false.
Definition MtieInit := false.
Definition MsieInit := false.

Definition isMemAscii := false.
Definition isMemRfArg := true.
Definition isRegsAscii := false.
Definition isRegsRfArg := true.
Definition pcCapReg := "pcCap".
Definition pcValReg := "pcVal".
Definition prevPcCapReg := "prevPcCap".
Definition prevPcValReg := "prevPcVal".
Definition justFenceIReg := "justFenceI".
Definition startFenceIReg := "startFenceI".
Definition waitForJustFenceIReg := "waitForJustFenceI".
Definition tagRead := "tagRead".
Definition tagWrite := "tagWrite".
Definition tagArray := "tagArray".
Definition tagRfString := "tagArrayFileArg".
Definition regsRead1 := "regsRead1".
Definition regsRead2 := "regsRead2".
Definition regsWrite := "regsWrite".
Definition regsArray := "regsArray".
Definition regsRfString := "regsArrayFileArg".
Definition memArray := "memArray".
Definition mtccReg := "MTCC".
Definition mtdcReg := "MTDC".
Definition mScratchCReg := "MScratchC".
Definition mepccReg := "MEPCC".
Definition mStatusReg := "MStatus".
Definition mieReg := "MIE".
Definition mCauseReg := "MCause".
Definition mtValReg := "MTVal".
Definition mTimeReg := "MTime".
Definition mTimeCmpReg := "MTimeCmp".
Definition mtiReg := "MTI".

Record MemBankInit :=
  { instRqName: string;
    loadRqName: string;
    storeRqName: string;
    memArrayName: string;
    memRfString: string }.

Definition prefixHex x n := ((x ++ "_") ++ natToHexStr n)%string.

Definition createMemRFParam (n: nat) : MemBankInit :=
  {|instRqName := prefixHex "instRq" n;
    loadRqName := prefixHex "loadRq" n;
    storeRqName := prefixHex "storeRq" n;
    memArrayName := prefixHex memArray n;
    memRfString := prefixHex "memArrayFileArg" n |}.

Definition memBankInits := map createMemRFParam (seq 0 8).

Class MemParams := {
    LgNumMemBytes: nat;
    LgNumMemBytesGt0: LgNumMemBytes > 0;
    (* NumMemBytes denotes the number of bytes in each bank. So total physical memory = NumMemBytes * NumBanks *)
    NumMemBytes := Nat.pow 2 LgNumMemBytes;
    memInit: type (Array NumMemBytes FullCapWithTag) }.

Class CoreConfigParams := {
    procName : string;
    memParams: MemParams;
    regsInit: type (Array NumRegs FullCapWithTag);
    pcCapInit: type Cap;
    pcValReducedInit: word (Xlen - 2);
    pcValInit := wcombine pcValReducedInit (wzero 2) : type Addr;
    pccValidThm: PccValid pcCapInit;
    hasTrap: bool;
    mtccCap: type Cap;
    mtccValReduced: word (Xlen - 2);
    mtccVal := wcombine mtccValReduced (wzero 2) : type Addr;
    mtdcCap: type Cap;
    mtdcValReduced: word (Xlen - 3);
    mtdcVal := wcombine mtdcValReduced (wzero 3) : type Addr;
    mScratchCCap: type Cap }.

Record InstProperties :=
  { hasCs1           : bool ;
    hasCs2           : bool ;
    hasCd            : bool ;
    hasScr           : bool ;
    hasCsr           : bool ;
    implicitReg      : word RegIdSz ;
    implicitScr      : word ScrIdSz ;
    implicitCsr      : word CsrIdSz ;
    signExt          : bool;
    isLoad           : bool ;
    isStore          : bool }.

Global Instance InstPropertiesEtaX : Settable _ :=
  settable!
    Build_InstProperties
  < hasCs1 ; hasCs2 ; hasCd; hasScr ; hasCsr ; implicitReg ; implicitScr ; implicitCsr ;
signExt ; isLoad ; isStore  >.

Definition DefProperties :=
  {|hasCs1           := false ;
    hasCs2           := false ;
    hasCd            := true ;
    hasScr           := false ;
    hasCsr           := false ;
    implicitReg      := wzero _ ;
    implicitScr      := wzero _ ;
    implicitCsr      := wzero _ ;
    signExt          := true ;
    isLoad           := false ;
    isStore          := false |}.

Definition FieldRange := {x: (nat * nat) & word (snd x)}.
Definition UniqId := (list FieldRange)%type.

Section Match.
  Variable ty: Kind -> Type.
  Local Open Scope kami_expr.

  Variable inst: Inst @# ty.

  Definition matchField (f: FieldRange) :=
    let '(existT (start, size) field) := f in
    UniBit (TruncMsb start size) (ZeroExtendTruncLsb (start + size) inst) ==
      Const ty field.

  Definition matchUniqId (uid: UniqId) :=
    CABool And (map matchField uid).
End Match.

Definition fieldVal range value : FieldRange :=
  existT (fun x => word (snd x)) range value.

Record ImmEncoder := {
    instPos : nat;
    immPos  : list (nat * nat) }.

Definition immFieldWidth (enc: ImmEncoder) :=
  (instPos enc, fold_right (fun '(_, val) accum => val + accum) 0 (immPos enc)).

Definition isGoodInstEncode (uniqId: UniqId) (immEncoder: list ImmEncoder)
  (instProperties: InstProperties) :=
  getDisjointContiguous
    ((if hasCs1 instProperties then [rs1FixedField] else []) ++
       (if hasCs2 instProperties then [rs2FixedField] else []) ++
       (if hasCd instProperties then [rdFixedField] else []) ++
       (if hasScr instProperties then [rs2FixedField] else []) ++
       (if hasCsr instProperties then [immField] else []) ++
       map (@projT1 _ _) uniqId ++
       map immFieldWidth immEncoder) = Some (snd instSizeField, InstSz).

Definition LdOp := 0.
Definition StOp := 1.
Definition MemOpSz := 1.

Definition LgNumBanks := Nat.log2_up NumBanks.
Definition MemSizeSz := LgNumBanks + 1.
Definition MemSize := Bit MemSizeSz.

Definition MemOpInfo :=
  STRUCT_TYPE {
      "op"    :: Bit MemOpSz;
      "size"  :: MemSize;
      "MC"    :: Bool;
      "LM"    :: Bool;
      "LG"    :: Bool;
      "sign?" :: Bool;
      "cap?"  :: Bool }.

Goal size MemOpInfo <= CapSz.
Proof.
  unfold MemOpInfo, MemOpSz, CapSz.
  simpl.
  lia.
Qed.

Definition FullOutput :=
  STRUCT_TYPE {
      "wb?" :: Bool;
      "cdTag" :: Bool;
      "cdCap" :: Cap;
      "cdVal" :: Data;
      "taken?" :: Bool;
      "pcMemAddr" :: Addr;
      "changePcCap?" :: Bool;
      "pcCap" :: Cap;
      "exception?" :: Bool;
      "exceptionCause" :: Data;
      "exceptionValue" :: Addr;
      "baseException?" :: Bool;
      "pcCapException?" :: Bool;
      "mem?" :: Bool;
      "memCap?" :: Bool;
      "memSize" :: MemSize;
      "store?" :: Bool;
      "ldSigned?" :: Bool;
      "ldPerms" :: CapPerms;
      "fenceI?" :: Bool;
      "wbScr?" :: Bool;
      "scrTag" :: Bool;
      "scrCap" :: Cap;
      "scrVal" :: Data;
      "scrException?" :: Bool;
      "wbCsr?" :: Bool;
      "csrVal" :: Data }.

Section ReadArray.
  Variable ty: Kind -> Type.
  Variable addrSz: nat.
  Variable addr: Bit addrSz @# ty.
  Variable n: nat.
  Variable arr: Array n (Bit 8) @# ty.
  Local Open Scope kami_expr.
  Definition readArrayConstSize (size: nat) :=
    BuildArray (fun (i: Fin.t size) => arr@[addr + $(FinFun.Fin2Restrict.f2n i)]).
End ReadArray.

Section InstEntry.
  Variable ik: Kind.
  Record InstEntry :=
    { instName       : string;
      uniqId         : UniqId;
      immEncoder     : list ImmEncoder;
      spec           : forall ty, FullCap @# ty -> Inst @# ty ->
                                  FullCapWithTag @# ty -> FullCapWithTag @# ty ->
                                  FullCapWithTag @# ty -> Data @# ty -> ik ## ty;
      instProperties : InstProperties;
      goodInstEncode : isGoodInstEncode uniqId immEncoder instProperties;
      immStart       : nat;
      immEnd         : nat;
      goodImmEncode  : getDisjointContiguous (concat (map immPos immEncoder)) = Some (immStart, immEnd)
    }.

  Record InstEntryFull := {
      xlens : list nat;
      extension: Extension;
      instEntries: list InstEntry }.

  Section Encoder.
    Variable i: InstEntry.
    Variable cs1 cs2 cd scr: word (snd rs1FixedField).
    Variable csr: word (snd immField).
    Variable immV: word Xlen.
    Fixpoint encodeImmField (imms: list (nat * nat)) :=
      match imms return word (fold_right (fun '(_, val) sum => sum + val) 0 imms) with
      | nil => WO
      | (start, width) :: xs => wcombine (encodeImmField xs) (extractWord immV start width)
      end.

    Definition encodeFullInstList :=
      fieldVal (0, 2) (2'b"11") ::
        (uniqId i ++
           map (fun ie => existT _ (instPos ie, _) (encodeImmField (immPos ie))) (immEncoder i) ++
           (if hasCs1 (instProperties i) then [existT _ rs1FixedField cs1] else []) ++
           (if hasCs2 (instProperties i) then [existT _ rs2FixedField cs2] else []) ++
           (if hasCd (instProperties i) then [existT _ rdFixedField cd] else []) ++
           (if hasScr (instProperties i) then [existT _ rs2FixedField scr] else []) ++
           (if hasCsr (instProperties i) then [existT _ immField csr] else [])).

    Definition encodeInst := @truncLsb InstSz _ ((wordCombiner (SigWordSort.sort encodeFullInstList))).
  End Encoder.

  Section Decoder.
    Variable inst: word InstSz.
    Fixpoint immDecoderHelp (instStart: nat) (ls: list (nat * nat)) : list FieldRange :=
      match ls with
      | nil => nil
      | (immStart, width) :: xs => existT _ (immStart, width) (extractWord inst instStart width) ::
                                     immDecoderHelp (instStart + width) xs
      end.

    Definition immDecoder (immEnc: ImmEncoder) :=
      immDecoderHelp (instPos immEnc) (immPos immEnc).

    Variable i: InstEntry.

    Definition decodePartialImmList :=
      SigWordSort.sort (concat (map immDecoder (immEncoder i))).

    Definition decodeImm: word Xlen :=
      match decodePartialImmList with
      | nil => wzero Xlen
      | existT (start, _) _ :: _ =>
          let res := wordCombiner (fieldVal (0, start) (wzero start) :: decodePartialImmList) in
          wconcat
            (if (andb (signExt (instProperties i)) (weqb (get_msb res) WO~1))
             then wones _
             else wzero (Xlen - (fold_right (fun new sum => sum + snd (projT1 new)) start decodePartialImmList)))
            res
      end.
  End Decoder.

  Section DecoderExpr.
    Variable ty: Kind -> Type.
    Variable inst: Inst @# ty.
    Fixpoint immDecIntervalHelp (instStart: nat) (ls: list (nat * nat)) : list (nat * (nat * nat)) :=
      match ls with
      | nil => nil
      | (immStart, width) :: xs => (immStart, (instStart, width)) :: immDecIntervalHelp (instStart + width) xs
      end.

    Definition immDecInterval (immEnc: ImmEncoder) :=
      immDecIntervalHelp (instPos immEnc) (immPos immEnc).

    Variable i: InstEntry.

    Definition decIntervals :=
      SigTripleSort.sort (concat (map immDecInterval (immEncoder i))).

    Definition decExprs := map (fun x =>
                                  existT (fun y => Bit (snd y) @# ty)
                                    (fst x, snd (snd x))
                                    (extractFieldExprDynamicWidth inst (fst (snd x)) (snd (snd x))))
                             decIntervals.

    Definition decodeImmExpr :=
      match decExprs with
      | nil => Const ty (wzero Xlen)
      | (existT (start, _) _) :: _ =>
          let res :=
            bitsCombiner (existT (fun y => Bit (snd y) @# ty) (0, start) (Const ty (wzero start)) :: decExprs) in
          if signExt (instProperties i)
          then SignExtendTruncLsb Xlen res
          else ZeroExtendTruncLsb Xlen res
      end.
  End DecoderExpr.
End InstEntry.

Definition InstEntrySpec := InstEntry FullOutput.

Record FuncEntryFull :=
  { funcNameFull        : string;
    localFuncInputFull  : Kind;
    localFuncFull       : forall ty, localFuncInputFull @# ty -> FullOutput ## ty;
    instsFull           : list (InstEntryFull localFuncInputFull) }.

Record FuncEntry :=
  { funcName        : string;
    localFuncInput  : Kind;
    localFunc       : forall ty, localFuncInput @# ty -> FullOutput ## ty;
    insts           : list (InstEntry localFuncInput) }.

Definition filterInsts k (ls: list (InstEntryFull k)) :=
  fold_right (fun new rest =>
                (if (existsb (Nat.eqb Xlen) (xlens new) &&
                       existsb (Extension_eqb (extension new)) supportedExts)%bool
                 then instEntries new
                 else []) ++ rest) [] ls.

Definition mkFuncEntry (fe : FuncEntryFull) :=
  {|funcName := funcNameFull fe;
    localFuncInput := localFuncInputFull fe;
    localFunc := localFuncFull fe;
    insts := filterInsts (instsFull fe)
  |}.

Record ScrReg :=
  { scrRegInfo    : RegInfo ScrIdSz;
    isLegal       : forall ty, Data @# ty -> Bool @# ty;
    legalize      : forall ty, Data @# ty -> Data @# ty }.

Record CsrReg :=
  { csrRegInfo    : RegInfo CsrIdSz;
    isSystemCsr   : bool;
    csrMask       : option (word Xlen) }.
