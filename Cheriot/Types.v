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
  Definition PccValid Xlen CapSz (capAccessors: CapAccessors CapSz Xlen) (pcCap: word CapSz) (pcAddr: word Xlen)
    (compressed: bool) :=
    evalLetExpr ( LETE perms <- getCapPerms capAccessors (Const type pcCap);
                  RetE (##perms @% "EX")) = true /\
      evalExpr ((isSealed capAccessors (Const _ pcCap))) = false /\
      (compressed = false -> truncLsb pcAddr = ZToWord 2 0).

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

(* Changes from CherIoT:
   - All PC out-of-bounds exceptions are caught only when executing
     the instruction, not during the previous instruction (like JALR,
     JAL, Branch, PC+2, PC+4).  Instead, we store the taken-ness and
     previous PC, which we use to set EPC on a taken branch/Jump.
 *)

Record MemBankInit numMemBytes :=
  { instRqName: string;
    loadRqName: string;
    storeRqName: string;
    memArrayName: string;
    regFileInit: RegFileInitT numMemBytes (Bit 8) }.

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
    IeInit: bool;
    MeieInit: bool;
    MtieInit: bool;
    MsieInit: bool;
    supportedExts: list Extension;
    extsHasBase: In Base supportedExts;
    RegIdSz: nat;
    regIdSzIs4_or5: RegIdSz = 4 \/ RegIdSz = 5;
    LgNumMemBytes: nat;
    (* NumMemBytes denotes the number of bytes in each bank. So total physical memory = NumBanks * NumMemBytes *)
    NumMemBytes := Nat.pow 2 LgNumMemBytes;
    MemBankParams := MemBankInit NumMemBytes;
    memBankInits: list MemBankParams;
    NumBanks := (CapSz + Xlen) / 8;
    lengthMemBankInits: length memBankInits = NumBanks;
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
    regsRead1: string;
    regsRead2: string;
    regsWrite: string;
    regsArray: string;
    Data := Bit Xlen;
    Cap := Bit CapSz;
    FullCapWithTag := STRUCT_TYPE { "tag" :: Bool;
                                    "cap" :: Cap;
                                    "val" :: Data };
    regsInit: RegFileInitT (Nat.pow 2 RegIdSz) FullCapWithTag }.

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

    Definition FieldRange := {x: (nat * nat) & word (snd x)}.
    Definition UniqId := (list FieldRange)%type.
    Definition fieldVal range value : FieldRange :=
      existT (fun x => word (snd x)) range value.

    Definition instSizeField := (0, 2).
    Definition opcodeField := (2, 5).
    Definition funct3Field := (12, 3).
    Definition funct7Field := (25, 7).
    Definition funct6Field := (26, 6).
    Definition immField := (20, 12).
    Definition rs1Field := (15, RegIdSz).
    Definition rs2Field := (20, RegIdSz).
    Definition rdField := (7, RegIdSz).
    Definition rs1FixedField := (15, 5).
    Definition rs2FixedField := (20, 5).
    Definition rdFixedField := (7, 5).
    Definition auiLuiField := (12, 20).

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
        implicitCsr : word (snd immField) }.
    
    Global Instance InstPropertiesEtaX : Settable _ :=
      settable!
        Build_InstProperties
      < hasCs1 ; hasCs2 ; hasCd; hasScr ; hasCsr ; implicitReg ; implicitScr ; implicitCsr >.
    
    Definition DefProperties :=
      {|hasCs1      := false ;
        hasCs2      := false ;
        hasCd       := true ;
        hasScr      := false ;
        hasCsr      := false ;
        implicitReg := 0 ;
        implicitScr := 0 ;
        implicitCsr := wzero _ |}.    
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

  Definition FuncOutput :=
    STRUCT_TYPE {
        "data"              :: FullCapWithTag;
        "pcOrScrCapOrMemOp" :: Cap;
        "addrOrScrOrCsrVal" :: Addr;
        "wb?"               :: Bool;
        "taken?"            :: Bool;
        "changePcCap?"      :: Bool;
        "mem?"              :: Bool;
        "exception?"        :: Bool;
        "baseException?"    :: Bool; (* non-cap exception *)
        "pcCapException?"   :: Bool; (* cap exception caused by PC *)
        "fenceI?"           :: Bool;
        "changeIe?"         :: Bool;
        "newIe"             :: Bool;
        "wbScr?"            :: Bool;
        "scrTag"            :: Bool;
        "scrException?"     :: Bool;
        "wbCsr?"            :: Bool}.

  Section ImmEncoder.
    Record ImmEncoder := {
        instPos : nat;
        immPos  : list (nat * nat)
      }.

    Definition immFieldWidth (enc: ImmEncoder) :=
      (instPos enc, fold_right (fun '(_, val) accum => val + accum) 0 (immPos enc)).

    Definition imm12   := [(0, 12)].
    Definition imm5    := [(0, 5)].
    Definition imm20_U := [(12, 20)].
    Definition imm20_J := [(12, 8); (11, 1); (1, 10); (20, 1)].
    Definition imm6    := [(0, 6)].
    Definition imm7    := [(5, 7)].
    Definition imm5_B  := [(11, 1); (1, 4)].
    Definition imm7_B  := [(5, 6); (12, 1)].
  End ImmEncoder.

  Section ImmVal.
    Variable immVal: word InstSz.
    Definition extractWord (start width: nat) : word width :=
      @truncMsb width (start + width) (@truncLsb (start + width) InstSz immVal).

    Fixpoint encodeImmField (imms: list (nat * nat)) :=
      match imms return word (fold_right (fun '(_, val) sum => val + sum) 0 imms) with
      | nil => WO
      | (start, width) :: xs => wcombine (extractWord start width) (encodeImmField xs)
      end.
  End ImmVal.

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

  Section InstEntry.
    Variable ik: Kind.
    Record InstEntry :=
      { instName       : string;
        uniqId         : UniqId;
        immEncoder     : list ImmEncoder;
        inputXform     : forall ty, FullCap @# ty -> Inst @# ty ->
                                    FullCapWithTag @# ty -> FullCapWithTag @# ty ->
                                    FullCapWithTag @# ty -> Data @# ty -> ik ## ty;
        instProperties : InstProperties;
        goodInstEncode : isGoodInstEncode uniqId immEncoder instProperties;
        goodImmEncode : exists x, getDisjointContiguous (concat (map immPos immEncoder)) = Some x
      }.

    Record InstEntryFull := {
        xlens : list nat;
        extension: Extension;
        instEntries: list InstEntry }.
  End InstEntry.

  Record FuncEntryFull :=
    { funcNameFull        : string;
      localFuncInputFull  : Kind;
      localFuncFull       : forall ty, localFuncInputFull @# ty -> FuncOutput ## ty;
      instsFull           : list (InstEntryFull localFuncInputFull) }.

  Record FuncEntry :=
    { funcName        : string;
      localFuncInput  : Kind;
      localFunc       : forall ty, localFuncInput @# ty -> FuncOutput ## ty;
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
End ParamDefinitions.
