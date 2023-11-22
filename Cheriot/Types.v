Require Import Kami.AllNotations.

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

Definition PccValid Xlen CapSz (capAccessors: CapAccessors CapSz Xlen) (pcCap: word CapSz) (pcAddr: word Xlen)
  (compressed: bool) :=
  evalLetExpr ( LETE perms <- getCapPerms capAccessors (Const type pcCap);
                RetE (Var type (SyntaxKind CapPerms) perms @% "EX"))%kami_expr = true /\
    evalExpr ((isSealed capAccessors (Const _ pcCap))) = false /\
    (compressed = false -> truncLsb pcAddr = ZToWord 2 0).

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
    TrapAddr: word (Xlen + CapSz);
    supportedExts: list Extension;
    extsHasBase: In Base supportedExts;
    RegIdSz: nat;
    regIdSzIs4_or5: RegIdSz = 4 \/ RegIdSz = 5;
    NumMemBytes: nat;
    MemBankParams := MemBankInit NumMemBytes;
    memBankInits: list MemBankParams;
    NumBanks := (CapSz + Xlen) / 8;
    lengthMemBankInits: length memBankInits = NumBanks;
    procName: string;
    pcCapReg: string;
    pcValReg: string;
    prevPcCapReg: string;
    prevPcValReg: string;
    takenReg: string;
    mtccTagReg: string; 
    mtccCapReg: string;
    mtccValReg: string;
    mtdcTagReg: string;
    mtdcCapReg: string;
    mtdcValReg: string;
    mscratchcTagReg: string;
    mscratchcCapReg: string;
    mscratchcValReg: string;
    mepccTagReg: string;
    mepccCapReg: string;
    mepccValReg: string;
    tagRead: string;
    tagWrite: string;
    tagArray: string }.

Section ParamDefinitions.
  Context {procParams: ProcParams}.

  Definition Data := Bit Xlen.
  Definition Addr := Bit Xlen.
  Definition Cap := Bit CapSz.

  Definition FullCap :=
    STRUCT_TYPE { "cap" :: Cap;
                  "val" :: Data }.

  Definition FullCapWithTag :=
    STRUCT_TYPE { "tag" :: Bool;
                  "cap" :: Cap;
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
    Definition funct5Field := (27, 5).
    Definition immField := (20, 12).
    Definition rmField := (12, 3).
    Definition fmtField := (25, 2).
    Definition rs1Field := (15, RegIdSz).
    Definition rs2Field := (20, RegIdSz).
    Definition rs3Field := (27, RegIdSz).
    Definition rdField := (7, RegIdSz).
    Definition rs1FixedField := (15, 5).
    Definition rs2FixedField := (20, 5).
    Definition rs3FixedField := (27, 5).
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
      Definition funct5 := extractFieldFromInst funct5Field.
      Definition imm := extractFieldFromInst immField.
      Definition rm := extractFieldFromInst rmField.
      Definition fmt := extractFieldFromInst fmtField.
      Definition branchOffset := {< (inst$[31:31]), (inst$[7:7]),  (inst$[30:25]), (inst$[11:8]), $$(WO~0) >}.
      Definition jalOffset := {< inst$[31:31], (inst$[19:12]), (inst$[20:20]), (inst$[30:21]), $$(WO~0) >}.
      Definition memSubOOpcode := {< (inst$[5:5]), (inst$[3:3])>}.
      Definition auiLuiOffset := extractFieldFromInst auiLuiField.
      Definition rs1 := extractFieldFromInstDynamic rs1Field.
      Definition rs2 := extractFieldFromInstDynamic rs2Field.
      Definition rs3 := extractFieldFromInstDynamic rs3Field.
      Definition rd := extractFieldFromInstDynamic rdField.
      Definition rs1Fixed := extractFieldFromInst rs1FixedField.
      Definition rs2Fixed := extractFieldFromInst rs2FixedField.
      Definition rs3Fixed := extractFieldFromInst rs3FixedField.
      Definition rdFixed := extractFieldFromInst rdFixedField.
    End Fields.

    Record InstProperties :=
      { hasCs1        : bool ;
        hasCs2        : bool ;
        hasScr        : bool ;
        hasCsr        : bool ;
        implicit      : nat ;
        implicitMepcc : bool ;
        implicitIe    : bool }.
  End InstEncoding.

  Definition FenceI := 0.
  Definition WFI := 1.

  Definition CapBoundsViolation  := 1.  (* Reg/PC *)
  Definition CapTagViolation     := 2.  (* Reg *)
  Definition CapSealViolation    := 3.  (* Reg *)
  Definition CapExecViolation    := 17. (* Reg *)
  Definition CapLdViolation      := 18. (* Reg *)
  Definition CapStViolation      := 19. (* Reg *)
  Definition CapLdCapViolation   := 20. (* Reg *)
  Definition CapStCapViolation   := 21. (* Reg *)
  Definition CapStLocalViolation := 22. (* Reg *)
  Definition CapSysRegViolation  := 24. (* PC *)
  Definition CapLdMisaligned     := 4.  (* Addr *)
  Definition CapStMisaligned     := 6.  (* Addr *)

  Definition InstMisaligned      := 0.  (* Addr *)
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
        "mayChangePc?"      :: Bool;
        "taken?"            :: Bool;
        "changePcCap?"      :: Bool;
        "mem?"              :: Bool;
        "exception?"        :: Bool;
        "baseException?"    :: Bool; (* non-cap exception *)
        "pcException?"      :: Bool; (* cap exception caused by PC *)
        "interrupt?"        :: Bool;
        "changeIe?"         :: Bool;
        "newIe"             :: Bool;
        "wbScr?"            :: Bool;
        "scrTag"            :: Bool;
        "scrException?"     :: Bool;
        "wbCsr?"            :: Bool}.

  Section InstEntry.
    Variable ik: Kind.
    Record InstEntry :=
      { instName       : string;
        uniqId         : UniqId;
        inputXform     : forall ty, FullCap @# ty -> Inst @# ty ->
                                    FullCapWithTag @# ty -> FullCapWithTag @# ty ->
                                    FullCapWithTag @# ty -> Data @# ty ->
                                    Bool @# ty -> ik ## ty;
        instProperties : InstProperties }.

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

  Definition mkFuncEntry (fe : FuncEntryFull) :=
    {|funcName := funcNameFull fe;
      localFuncInput := localFuncInputFull fe;
      localFunc := localFuncFull fe;
      insts :=
        fold_left (fun prev new =>
                     (if (getBool (in_dec Nat.eq_dec Xlen (xlens new)) &&
                            getBool (in_dec Extension_eq_dec (extension new) supportedExts))%bool
                      then instEntries new
                      else []) ++ prev)
          (instsFull fe) []
    |}.

  Record CsrInfo := {
      csrAddress : word (snd (immField));
      csrReg : RegInitT }.

  Definition callReadRegFile k (name: string) ty n (idx: Bit n @# ty) : ActionT ty k :=
    ( Call ret : Array 1 k <- name (idx: Bit n);
      Ret (ReadArrayConst #ret Fin.F1) )%kami_action.
    
  Definition callWriteRegFile (name: string) ty n (idx: Bit n @# ty) k (v: k @# ty) : ActionT ty Void :=
    ( Call name (STRUCT { "addr" ::= idx;
                          "data" ::= BuildArray (fun _ => v) } : WriteRq n (Array 1 k));
      Retv )%kami_action.
End ParamDefinitions.
