Require Import Kami.AllNotations ProcKami.Cheriot.Lib.
Require Import RecordUpdate.RecordUpdate.
  
Section CapAccessors.
  Variable CapSz: nat.
  Variable AddrSz: nat.

  Definition CapPerms :=
    STRUCT_TYPE {
        "U0" :: Bool;
        "SE" :: Bool; (* Permit Seal *)
        "US" :: Bool; (* Permit Unseal *)
        "EX" :: Bool; (* Permit Execute *)
        "SR" :: Bool; (* Permit system register access *)
        "MC" :: Bool; (* Permit Load or Store of Caps *)
        "LD" :: Bool; (* Permit Load *)
        "SL" :: Bool; (* Permit Store of Local *)
        "LM" :: Bool; (* Permit Mutability of loaded cap, i.e. allow store using the cap *)
        "SD" :: Bool; (* Permit Store *)
        "LG" :: Bool; (* Permit Store into Global of loaded cap *)
        "GL" :: Bool }. (* Global *)

  Record CapAccessors := {
      CapRSz: nat;
      getCapR: forall ty, Bit CapSz @# ty -> Bit CapRSz @# ty;
      setCapR: forall ty, Bit CapRSz @# ty -> Bit CapSz @# ty -> Bit CapSz @# ty;
      CapPSz: nat;
      getCapP: forall ty, Bit CapSz @# ty -> Bit CapPSz @# ty;
      setCapP: forall ty, Bit CapPSz @# ty -> Bit CapSz @# ty -> Bit CapSz @# ty;
      CapOTypeSz: nat;
      getCapOType: forall ty, Bit CapSz @# ty -> Bit CapOTypeSz @# ty;
      setCapOType: forall ty, Bit CapOTypeSz @# ty -> Bit CapSz @# ty -> Bit CapSz @# ty;
      CapESz: nat;
      getCapE: forall ty, Bit CapSz @# ty -> Bit CapESz @# ty;
      setCapE: forall ty, Bit CapESz @# ty -> Bit CapSz @# ty -> Bit CapSz @# ty;
      CapBSz: nat;
      getCapB: forall ty, Bit CapSz @# ty -> Bit CapBSz @# ty;
      setCapB: forall ty, Bit CapBSz @# ty -> Bit CapSz @# ty -> Bit CapSz @# ty;
      CapTSz: nat;
      getCapT: forall ty, Bit CapSz @# ty -> Bit CapTSz @# ty;
      setCapT: forall ty, Bit CapTSz @# ty -> Bit CapSz @# ty -> Bit CapSz @# ty;
      getCapEFromExp: forall ty, Bit (Nat.log2_up AddrSz) @# ty -> Bit CapESz @# ty;
      getCapExpFromE: forall ty, Bit CapESz @# ty -> Bit (Nat.log2_up AddrSz) @# ty;
      isSealed: forall ty, Bit CapSz @# ty -> Bool @# ty;
      isSentry: forall ty, Bit CapSz @# ty -> Bool @# ty;
      isIeSentry: forall ty, Bit CapSz @# ty -> Bool @# ty;
      isIdSentry: forall ty, Bit CapSz @# ty -> Bool @# ty;
      getOTypeFromIe: forall ty, Bool @# ty (* Interrupt Enabled ? *) -> Bit CapOTypeSz @# ty;
      seal: forall ty, Bit CapOTypeSz @# ty -> Bit CapSz @# ty -> Bit CapSz @# ty;
      unseal: forall ty, Bit CapSz @# ty -> Bit CapSz @# ty;
      isSealAddr: forall ty, Bit AddrSz @# ty -> Bool @# ty (* Exec seal or not *) -> Bool @# ty;
      getCapPerms: forall ty, Bit CapSz @# ty -> CapPerms ## ty;
      setCapPerms: forall ty, CapPerms @# ty -> Bit CapSz @# ty -> Bit CapSz ## ty;
      BaseTop := STRUCT_TYPE {
                     "base" :: Bit AddrSz;
                     "top"  :: Bit (AddrSz + 1);
                     "aTopBase" :: Bit (AddrSz - CapBSz) };
      getCapBaseTop: forall ty, Bit CapSz @# ty -> Bit AddrSz @# ty -> BaseTop ## ty;
      CapBounds := STRUCT_TYPE {
                       "B" :: Bit CapBSz;
                       "T" :: Bit CapTSz;
                       "exp" :: Bit (Nat.log2_up AddrSz);
                       "exact?" :: Bool };
      getCapBounds: forall ty, Bit AddrSz @# ty (* Base *) -> Bit AddrSz @# ty (* Length *) -> CapBounds ## ty;
      setCapBounds ty (cap: Bit CapSz @# ty) B T exp :=
        setCapE (getCapEFromExp exp) (setCapT T (setCapB B cap))
    }.
End CapAccessors.

Inductive Extension := Base | M.

Theorem Extension_eq_dec: forall (e1 e2: Extension), {e1 = e2} + {e1 <> e2}.
Proof.
  decide equality.
Qed.

Section VarType.
  Local Notation "## x" := (Var type (SyntaxKind _) x) (no associativity, at level 0).

  Local Open Scope kami_expr.
  Definition PcCapValid Xlen CapSz (capAccessors: CapAccessors CapSz Xlen) (pcCap: word CapSz) :=
    evalLetExpr (LETE perms <- getCapPerms capAccessors (Const type pcCap);
                 RetE (##perms @% "EX")) = true /\
      evalExpr ((isSealed capAccessors (Const _ pcCap))) = false.

  Definition PcValValid Xlen (pcAddr: word Xlen) (compressed: bool) :=
    compressed = false -> truncLsb pcAddr = ZToWord 2 0.
  Definition PccValid Xlen CapSz (capAccessors: CapAccessors CapSz Xlen) (pcCap: word CapSz) (pcAddr: word Xlen)
    (compressed: bool) :=
    PcCapValid capAccessors pcCap /\ PcValValid pcAddr compressed.

  Definition MtccValid Xlen CapSz (capAccessors: CapAccessors CapSz Xlen)
    (mtccCap: word CapSz) (mtccVal: word Xlen) :=
    evalLetExpr ( LETE perms <- getCapPerms capAccessors (Const type mtccCap);
                  LETC sealed <- isSealed capAccessors (Const type mtccCap);
                  LETC aligned <- isZero (ZeroExtendTruncLsb 2 (Const type mtccVal));
                  LETE baseTop <- getCapBaseTop capAccessors (Const type mtccCap) (Const type mtccVal);
                  LETC baseBound <- Const type mtccVal >= (##baseTop @% "base");
                  LETC topBound <- (ZeroExtend 1 (Const type mtccVal) + Const type (natToWord _ 4) <=
                                      (##baseTop @% "top"));
                  RetE ((##perms @% "EX") && (##perms @% "SR") && !##sealed && ##aligned
                        && (##baseBound && ##topBound))) = true.

  Definition MtdcValid Xlen CapSz (capAccessors: CapAccessors CapSz Xlen)
    (mtdcCap: word CapSz) (mtdcVal: word Xlen) :=
    evalLetExpr ( LETE baseTop <- getCapBaseTop capAccessors (Const type mtdcCap) (Const type mtdcVal);
                  LETC baseBound <- Const type mtdcVal >= (##baseTop @% "base");
                  LETC topBound <- (ZeroExtend 1 (Const type mtdcVal) + Const type (natToWord _ 8) <=
                                      (##baseTop @% "top"));
                  RetE (##baseBound && ##topBound)) = true.  
End VarType.

Record MemBankInit :=
  { instRqName: string;
    loadRqName: string;
    storeRqName: string;
    memArrayName: string;
    memRfString: string }.

Class ProcParams :=
  { Xlen: nat;
    xlenIs32_or_64: Xlen = 32 \/ Xlen = 64;
    CapSz := Xlen;
    capAccessors: CapAccessors CapSz Xlen;
    PcCap: word CapSz;
    PcAddr: word Xlen;
    compressed: bool;
    pccValid: PccValid capAccessors PcCap PcAddr compressed;
    ExecRootCap: word CapSz;
    DataRootCap: word CapSz;
    SealRootCap: word CapSz;
    MtccVal: word Xlen;
    MtdcVal: word Xlen;
    IeInit: bool;
    MeieInit: bool;
    MtieInit: bool;
    MsieInit: bool;
    supportedExts: list Extension;
    extsHasBase: In Base supportedExts;
    RegIdSz: nat;
    regIdSzIs4_or5: RegIdSz = 4 \/ RegIdSz = 5;
    LgNumMemBytes: nat;
    (* NumMemBytes denotes the number of bytes in each bank. So total physical memory = NumMemBytes * NumBanks *)
    NumMemBytes := Nat.pow 2 LgNumMemBytes;
    memBankInits: list MemBankInit;
    NumBanks := (Xlen + CapSz) / 8;
    lengthMemBankInits: length memBankInits = NumBanks;
    isMemAscii: bool;
    isMemRfArg: bool;
    memInit: Fin.t (NumMemBytes * NumBanks) -> word 8;
    procName: string;
    pcCapReg: string;
    pcValReg: string;
    prevPcCapReg: string;
    prevPcValReg: string;
    justFenceIReg: string;
    startFenceIReg: string;
    reqJustFenceIReg: string;
    tagRead: string;
    tagWrite: string;
    tagArray: string;
    memArray: string;
    regsRead1: string;
    regsRead2: string;
    regsWrite: string;
    regsArray: string;
    Data := Bit Xlen;
    Cap := Bit CapSz;
    FullCapWithTag := STRUCT_TYPE { "tag" :: Bool;
                                    "cap" :: Cap;
                                    "val" :: Data };
    isRegsAscii: bool;
    isRegsRfArg: bool;
    regsRfString: string;
    regsInit: Fin.t (Nat.pow 2 RegIdSz) -> ConstT FullCapWithTag;
    hasTrap: bool }.

Section ParamDefinitions.
  Context {procParams: ProcParams}.

  Definition Addr := Bit Xlen.

  Definition FullCap :=
    STRUCT_TYPE { "cap" :: Cap;
                  "val" :: Data }.

  Section Ty.
    Variable ty: Kind -> Type.
    Local Open Scope kami_expr.
    Definition mkFullCap (cap : Cap @# ty) (val : Data @# ty) :=
      STRUCT { "cap" ::= cap;
               "val" ::= val }.

    Definition mkFullCapWithTag (tag : Bool @# ty) (cap : Cap @# ty)
      (val : Data @# ty) :=
      STRUCT { "tag" ::= tag;
               "cap" ::= cap;
               "val" ::= val }.
  End Ty.

  Section InstEncoding.
    Definition RegId := Bit RegIdSz.
    Definition RegFixedIdSz := 5.
    Definition NumRegs := 2^RegIdSz.
    Definition InstSz := 32.
    Definition Inst := (Bit InstSz).
    Definition CompInstSz := 16.
    Definition CompInst := (Bit CompInstSz).
    Definition ScrIdSz := 5.
    Definition ScrId := Bit ScrIdSz.

    Definition isInstNotCompressed ty sz (bitString : Bit sz @# ty)
      := unpack Bool (UniBit (UAnd _) (ZeroExtendTruncLsb 2 bitString)).

    Definition isInstCompressed ty sz (bitString : Bit sz @# ty) :=
      (!(isInstNotCompressed (bitString)))%kami_expr.

    Definition instSizeField := (0, 2).
    Definition opcodeField := (2, 5).
    Definition funct3Field := (12, 3).
    Definition funct7Field := (25, 7).
    Definition funct6Field := (26, 6).
    Definition immField := (20, 12).
    Definition rs1Field := (15, RegIdSz).
    Definition rs2Field := (20, RegIdSz).
    Definition rdField := (7, RegIdSz).
    Definition rs1FixedField := (15, RegFixedIdSz).
    Definition rs2FixedField := (20, RegFixedIdSz).
    Definition rdFixedField := (7, RegFixedIdSz).
    Definition auiLuiField := (12, 20).

    Definition imm12   := [(0, 12)].
    Definition imm5    := [(0, 5)].
    Definition imm20_U := [(12, 20)].
    Definition imm20_J := [(12, 8); (11, 1); (1, 10); (20, 1)].
    Definition imm6    := [(0, 6)].
    Definition imm7    := [(5, 7)].
    Definition imm5_B  := [(11, 1); (1, 4)].
    Definition imm7_B  := [(5, 6); (12, 1)].

    Section Fields.
      Variable ty: Kind -> Type.
      Variable inst: Inst @# ty.

      Local Open Scope kami_expr.

      Notation extractFieldFromInst span := (extractFieldExpr InstSz inst (fst span) (snd span)).

      Notation extractFieldFromInstDynamic span := (extractFieldExprDynamicWidth inst (fst span) (snd span)).
      
      Definition instSize := extractFieldFromInst instSizeField.
      Definition opcode := extractFieldFromInst opcodeField.
      Definition funct3 := extractFieldFromInst funct3Field.
      Definition funct7 := extractFieldFromInst funct7Field.
      Definition funct6 := extractFieldFromInst funct6Field.
      Definition imm := extractFieldFromInst immField.
      Definition branchOffset := ({< extractFieldFromInst (31, 1),
                                     extractFieldFromInst ( 7, 1),
                                     extractFieldFromInst (25, 6),
                                     extractFieldFromInst ( 8, 4), $$(WO~0) >}).
      Definition jalOffset := ({< extractFieldFromInst (31,  1),
                                  extractFieldFromInst (12,  8),
                                  extractFieldFromInst (20,  1),
                                  extractFieldFromInst (21, 10), $$(WO~0) >}).
      Definition auiLuiOffset := extractFieldFromInst auiLuiField.
      Definition rs1 := extractFieldFromInstDynamic rs1Field.
      Definition rs2 := extractFieldFromInstDynamic rs2Field.
      Definition rd := extractFieldFromInstDynamic rdField.
      Definition rs1Fixed := extractFieldFromInst rs1FixedField.
      Definition rs2Fixed := extractFieldFromInst rs2FixedField.
      Definition rdFixed := extractFieldFromInst rdFixedField.
    End Fields.

    Record InstProperties :=
      { hasCs1      : bool ;
        hasCs2      : bool ;
        hasCd       : bool ;
        hasScr      : bool ;
        hasCsr      : bool ;
        implicitReg : nat ;
        implicitScr : nat ;
        implicitCsr : word (snd immField);
        signExt     : bool;
        isLoad      : bool ;
        isStore     : bool }.

    Global Instance InstPropertiesEtaX : Settable _ :=
      settable!
        Build_InstProperties
      < hasCs1 ; hasCs2 ; hasCd; hasScr ; hasCsr ; implicitReg ; implicitScr ; implicitCsr ;
        signExt ; isLoad ; isStore  >.
    
    Definition DefProperties :=
      {|hasCs1      := false ;
        hasCs2      := false ;
        hasCd       := true ;
        hasScr      := false ;
        hasCsr      := false ;
        implicitReg := 0 ;
        implicitScr := 0 ;
        implicitCsr := wzero _ ;
        signExt     := true ;
        isLoad      := false ;
        isStore     := false |}.

    Definition FieldRange := {x: (nat * nat) & word (snd x)}.
    Definition UniqId := (list FieldRange)%type.

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
  End InstEncoding.

  Definition CapException        := N.to_nat (hex "1c").
  Definition CapBoundsViolation  := 1.  (* Reg/PC *)
  Definition CapTagViolation     := 2.  (* Reg *)
  Definition CapSealViolation    := 3.  (* Reg *)
  Definition CapExecViolation    := 17. (* Reg *)
  Definition CapLdViolation      := 18. (* Reg *)
  Definition CapStViolation      := 19. (* Reg *)
  Definition CapStCapViolation   := 21. (* Reg *)
  Definition CapStLocalViolation := 22. (* Reg *)
  Definition CapSysRegViolation  := 24. (* PC *)
  Definition CapLdMisaligned     := 4.  (* Addr *)
  Definition CapStMisaligned     := 6.  (* Addr *)

  Definition InstMisaligned      := 0.  (* Addr *)
  Definition InstAccessFault     := 1.  (* Addr *)
  Definition InstPageFault       := 12. (* Addr *)
  Definition LoadAccessFault     := 5.  (* Addr *)
  Definition LoadPageFault       := 13. (* Addr *)
  Definition StoreAccessFault    := 7.  (* Addr *)
  Definition StorePageFault      := 15. (* Addr *)
  Definition TagAccessFault      := 24. (* Addr *)
  Definition TagPageFault        := 25. (* Addr *)
  Definition InstIllegal         := 2.  (* Inst *)
  Definition ECall               := 8.

  Definition LdOp := 0.
  Definition StOp := 1.
  Definition MemOpSz := 1.

  Definition MemSizeSz := (Nat.log2_up ((Xlen + CapSz)/8)) + 1.
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

  Theorem sizeMemOpInfo: size MemOpInfo <= CapSz.
  Proof.
    simpl.
    unfold MemSize, MemSizeSz, CapSz, Xlen, MemOpSz.
    destruct procParams as [xlen xlen_vars].
    destruct xlen_vars; subst; simpl; lia.
  Qed.

  Definition ExpandedCap : Kind :=
    STRUCT_TYPE { "R"     :: Bit 1 ;
                  "p"     :: CapPerms;
                  "oType" :: Bit 3;
                  "base"  :: Addr;
                  "top"   :: Addr }.

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
        "changeIe?" :: Bool;
        "newIe" :: Bool;
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
      Variable cs1 cs2 cd: word (snd rs1FixedField).
      Variable csr: word (snd immField).
      Variable immV: word Xlen.
      Fixpoint encodeImmField (imms: list (nat * nat)) :=
        match imms return word (fold_right (fun '(_, val) sum => sum + val) 0 imms) with
        | nil => WO
        | (start, width) :: xs => wcombine (encodeImmField xs) (extractWord immV start width)
        end.

      Definition encodeFullInstList :=
        uniqId i ++
          map (fun ie => existT _ (instPos ie, _) (encodeImmField (immPos ie))) (immEncoder i) ++
          (if hasCs1 (instProperties i) then [existT _ rs1FixedField cs1] else []) ++
          (if hasCs2 (instProperties i) then [existT _ rs2FixedField cs2] else []) ++
          (if hasCd (instProperties i) then [existT _ rdFixedField cd] else []) ++
          (if hasScr (instProperties i) then [existT _ rs2FixedField cs2] else []) ++
          (if hasCsr (instProperties i) then [existT _ immField csr] else []).

      Definition encodeInst := @truncLsb InstSz _ ((wordCombiner (2'b"11") (SigWordSort.sort encodeFullInstList))).
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
            let res := wordCombiner (wzero start) decodePartialImmList in
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
                                    existT (fun x => Bit (snd x) @# ty)
                                      (fst x, snd (snd x)) (extractBits inst (fst (snd x)) (snd (snd x))))
                               decIntervals.

      Definition decodeImmExpr :=
        match decExprs with
        | nil => Const ty (wzero Xlen)
        | (existT (start, _) _) :: _ =>
            let res := bitsCombiner (Const ty (wzero start)) decExprs in
            if signExt (instProperties i)
            then SignExtendTruncLsb Xlen res
            else ZeroExtendTruncLsb Xlen res
        end.
    End DecoderExpr.
  End InstEntry.

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
                  (if (getBool (in_dec Nat.eq_dec Xlen (xlens new)) &&
                         getBool (in_dec Extension_eq_dec (extension new) supportedExts))%bool
                   then instEntries new
                   else []) ++ rest) [] ls.
  
  Definition mkFuncEntry (fe : FuncEntryFull) :=
    {|funcName := funcNameFull fe;
      localFuncInput := localFuncInputFull fe;
      localFunc := localFuncFull fe;
      insts := filterInsts (instsFull fe)
    |}.

  Record ScrReg :=
    { scrRegInfo    : RegInfo (snd rs2FixedField) FullCapWithTag;
      isLegal       : forall ty, Data @# ty -> Bool @# ty;
      legalize      : forall ty, Data @# ty -> Data @# ty }.

  Record CsrReg :=
    { csrRegInfo    : RegInfo (snd immField) Data;
      isSystemCsr   : bool;
      csrMask       : option (word Xlen) }.

  Theorem XlenSXlenMinus1: Xlen = ((S (Xlen - 1)) * 1)%nat.
  Proof.
    destruct procParams as [xlen xlen_vars].
    destruct xlen_vars; subst; simpl; lia.
  Qed.

  Section ReadArray.
    Variable ty: Kind -> Type.
    Variable addr: Addr @# ty.
    Variable n: nat.
    Variable arr: Array n (Bit 8) @# ty.
    Local Open Scope kami_expr.
    Definition readArrayConstSize (size: nat) :=
      BuildArray (fun (i: Fin.t size) => arr@[addr + $(FinFun.Fin2Restrict.f2n i)]).
  End ReadArray.
End ParamDefinitions.
