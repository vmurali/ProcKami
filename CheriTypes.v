Require Import Kami.AllNotations.

Import ListNotations.

Section CapAccessors.
  Variable CapSz: nat.
  Variable AddrSz: nat.

  Definition CapPerms :=
    STRUCT_TYPE {
        "U0" :: Bool;
        "SE" :: Bool; (* Permit Seal *)
        "US" :: Bool; (* Permit Unseal *)
        "EX" :: Bool; (* Permit Execute *)
        "SR" :: Bool; (* Permit system register access. Unused *)
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
      BaseTop := STRUCT_TYPE {
                     "base" :: Bit AddrSz;
                     "top"  :: Bit (AddrSz + 1) };
      getCapBaseTop: forall ty, Bit CapSz @# ty -> Bit AddrSz @# ty -> BaseTop ## ty;
      isSealed: forall ty, Bit CapSz @# ty -> Bool @# ty;
      isSentry: forall ty, Bit CapSz @# ty -> Bool @# ty;
      getCapPerms: forall ty, Bit CapSz @# ty -> CapPerms ## ty;
      getOTypeFromIe: forall ty, Bool @# ty (* Interrupt Enabled ? *) -> Bit CapOTypeSz @# ty;
      seal: forall ty, Bit CapSz @# ty -> Bit CapSz @# ty -> Bit CapSz @# ty;
      unseal: forall ty, Bit CapSz @# ty -> Bit AddrSz @# ty -> Bit CapSz @# ty;
      isIeSentry: forall ty, Bit CapSz @# ty -> Bool @# ty;
      isIdSentry: forall ty, Bit CapSz @# ty -> Bool @# ty;
      setCapPerms: forall ty, Bit CapSz @# ty -> CapPerms @# ty -> Bit CapSz ## ty;
      isSealAddr: forall ty, Bit AddrSz @# ty -> Bool @# ty (* Exec seal or not *) -> Bool @# ty;
      getCapEFromExp: forall ty, Bit (Nat.log2_up AddrSz) @# ty -> Bit CapESz @# ty;
      getCapExpFromE: forall ty, Bit CapESz @# ty -> Bit (Nat.log2_up AddrSz) @# ty;
      CapBounds := STRUCT_TYPE {
                       "B" :: Bit CapBSz;
                       "T" :: Bit CapTSz;
                       "exp" :: Bit (Nat.log2_up AddrSz);
                       "exact?" :: Bool };
      getCapBounds: forall ty, Bit AddrSz @# ty (* Base *) -> Bit AddrSz @# ty (* Length *) -> CapBounds ## ty
    }.
End CapAccessors.

Inductive Extension := Base | M.

Definition PccValid Xlen CapSz (capAccessors: CapAccessors CapSz Xlen) (pcCap: word CapSz) (pcAddr: word Xlen)
  (compressed: bool) :=
  evalLetExpr ( LETE perms <- getCapPerms capAccessors (Const type pcCap);
                RetE (Var type (SyntaxKind CapPerms) perms @% "EX"))%kami_expr = true /\
    evalExpr ((isSealed capAccessors (Const _ pcCap))) = false /\
    if compressed then truncLsb pcAddr = ZToWord 2 0 else True.

(* Changes from CherIoT:
   - AUIPCC, AUICGP, CIncAddr and CSetAddr checks for bounds before clearing the tag
     instead of representability checks
   - All PC out-of-bounds exceptions are caught only when executing the instruction,
     not during the previous instruction (like JALR, JAL, Branch, PC+2, PC+4)
 *)

Class ProcParams :=
  { procName: string;
    Xlen: nat;
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
    regIdSzIs4_or5: RegIdSz = 4 \/ RegIdSz = 5
  }.

Notation "@^ x" := (procName ++ "_" ++ x)%string (at level 0).

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

    Definition isInstCompressed ty sz (bitString : Bit sz @# ty)
      := (ZeroExtendTruncLsb 2 bitString != $$(('b"11") : word 2))%kami_expr.

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

      Notation extractField span :=
        (UniBit (TruncMsb (fst span) (snd span))
           (UniBit (TruncLsb (fst span + snd span) (InstSz - (fst span + snd span))) inst)).

      Notation extractFieldDynamic span :=
        (UniBit (TruncLsb (fst span) (snd span))
           (ZeroExtendTruncLsb (fst span + snd span) inst)).
      
      Definition instSize := extractField instSizeField.
      Definition opcode := extractField opcodeField.
      Definition funct3 := extractField funct3Field.
      Definition funct7 := extractField funct7Field.
      Definition funct6 := extractField funct6Field.
      Definition funct5 := extractField funct5Field.
      Definition imm := extractField immField.
      Definition rm := extractField rmField.
      Definition fmt := extractField fmtField.
      Definition branchOffset := {< (inst$[31:31]), (inst$[7:7]),  (inst$[30:25]), (inst$[11:8]), $$(WO~0) >}.
      Definition jalOffset := {< inst$[31:31], (inst$[19:12]), (inst$[20:20]), (inst$[30:21]), $$(WO~0) >}.
      Definition memSubOOpcode := {< (inst$[5:5]), (inst$[3:3])>}.
      Definition auiLuiOffset := extractField auiLuiField.
      Definition rs1 := extractFieldDynamic rs1Field.
      Definition rs2 := extractFieldDynamic rs2Field.
      Definition rs3 := extractFieldDynamic rs3Field.
      Definition rd := extractFieldDynamic rdField.
      Definition rs1Fixed := extractField rs1FixedField.
      Definition rs2Fixed := extractField rs2FixedField.
      Definition rs3Fixed := extractField rs3FixedField.
      Definition rdFixed := extractField rdFixedField.
    End Fields.

    Record InstProperties :=
      { hasCs1   : bool ;
        hasCs2   : bool ;
        implicit : nat }.
  End InstEncoding.

  Definition FenceI := 0.
  Definition Wfi := 1.

  Definition CapBoundsViolation  := 1.  (* Reg/PC *)
  Definition CapTagViolation     := 2.  (* Reg *)
  Definition CapSealViolation    := 3.  (* Reg *)
  Definition CapExecViolation    := 17. (* Reg *)
  Definition CapLdViolation      := 18. (* Reg *)
  Definition CapStViolation      := 19. (* Reg *)
  Definition CapLdCapViolation   := 20. (* Reg *)
  Definition CapStCapViolation   := 21. (* Reg *)
  Definition CapStLocalViolation := 22. (* Reg *)
  Definition CapLdMisaligned     := 4.  (* Addr *)
  Definition InstMisaligned      := 0.  (* Addr *)
  Definition CapStMisaligned     := 6.  (* Addr *)

  Definition LdOp := 0.
  Definition StOp := 1.
  Definition MemOpSz := 1.

  Definition MemSizeSz := Nat.log2_up (S ((Xlen + CapSz)/8)).
  Definition MemSize := Bit MemSizeSz.

  Definition MemOpInfo :=
    STRUCT_TYPE {
        "memOp"      :: Bit MemOpSz;
        "size"       :: MemSize;
        "signExt?"   :: Bool;
        "MC"         :: Bool;
        "LM"         :: Bool;
        "LG"         :: Bool;
        "accessTag?" :: Bool }.

  Theorem sizeMemOpInfo: size MemOpInfo <= CapSz.
  Proof.
    simpl.
    unfold MemSize, MemSizeSz, CapSz, Xlen, MemOpSz.
    destruct procParams as [_ xlen xlen_vars _ _ _ _ _ _ _ _ _ _ _ _ _ _].
    destruct xlen_vars; subst; simpl; lia.
  Qed.

  (* Regular      : (wb?, data: FullCapWithTag, pcUpd?, addr: FullCap, regFile: Bit 0,
                     exception?, exceptionCause: Bit ExceptionCauseSz=5, Reg/Pc: Bit 1)
     Mem          : (memOp: MemOpInfo, data: FullCapWithTag, addr: Addr,
                     exception?, exceptionCause: Bit ExceptionCauseSz=5)
     SyncInterrupt: (syncInterruptCause: Bit SyncInterruptSz=1) *)

  Definition FuncOutput :=
    STRUCT_TYPE {
        "data"             :: FullCapWithTag;
        "addrCapOrMemOp"   :: Cap;
        "addr"             :: Addr;
        "interruptOrBJal?" :: Bool;
        "wb?"              :: Bool;
        "pcUpd?"           :: Bool;
        "mem?"             :: Bool;
        "exception?"       :: Bool;
        "changeIe?"        :: Bool;
        "ie?"              :: Bool }.

  Section FuncOutputHelpers.
    Variable ty: Kind -> Type.
    Variable dataVal: Data @# ty. (* Default for Base Func Unit: Result of Adder *)
    Variable addrCap: Cap @# ty.  (* Default for Base Func Unit: Result of old PCC cap *)
    Variable addrVal: Addr @# ty. (* Default for Base Func Unit: Result of Cap's address *)

    Local Open Scope kami_expr.

    Definition intResult dVal : FullCapWithTag @# ty :=
      STRUCT { "tag" ::= $$false;
               "cap" ::= $0;
               "val" ::= dVal }.

    Definition mkNoUpd : FuncOutput @# ty :=
      STRUCT {
          "data"             ::= intResult dataVal;
          "addrCapOrMemOp"   ::= addrCap;
          "addr"             ::= addrVal;
          "interruptOrBJal?" ::= $$false;
          "wb?"              ::= $$false;
          "pcUpd?"           ::= $$false;
          "mem?"             ::= $$false;
          "exception?"       ::= $$false;
          "changeIe?"        ::= $$false;
          "ie?"              ::= $$false }.

    Definition mkIntReg : FuncOutput @# ty :=
      STRUCT {
          "data"             ::= intResult dataVal;
          "addrCapOrMemOp"   ::= addrCap;
          "addr"             ::= addrVal;
          "interruptOrBJal?" ::= $$false;
          "wb?"              ::= $$true;
          "pcUpd?"           ::= $$false;
          "mem?"             ::= $$false;
          "exception?"       ::= $$false;
          "changeIe?"        ::= $$false;
          "ie?"              ::= $$false }.

    Definition mkPc (pcUpd: Bool @# ty) (exception: Pair Bool Data @# ty) : FuncOutput @# ty :=
      STRUCT {
          "data"             ::= intResult (exception @% "snd");
          "addrCapOrMemOp"   ::= addrCap;
          "addr"             ::= addrVal;
          "interruptOrBJal?" ::= (exception @% "fst");
          "wb?"              ::= $$false;
          "pcUpd?"           ::= (!(exception @% "fst") && pcUpd);
          "mem?"             ::= $$false;
          "exception?"       ::= (exception @% "fst");
          "changeIe?"        ::= $$false;
          "ie?"              ::= $$false }.

    Definition mkCapResult (dataTag: Bool @# ty) : FuncOutput @# ty :=
      STRUCT {
          "data"             ::= STRUCT {
                                     "tag" ::= dataTag;
                                     "cap" ::= addrCap;
                                     "val" ::= dataVal };
          "addrCapOrMemOp"   ::= addrCap;
          "addr"             ::= addrVal;
          "interruptOrBJal?" ::= $$false;
          "wb?"              ::= $$true;
          "pcUpd?"           ::= $$false;
          "mem?"             ::= $$false;
          "exception?"       ::= $$false;
          "changeIe?"        ::= $$false;
          "ie?"              ::= $$false }.
      
    Definition mkIntRegAndPc (dataTag: Bool @# ty) (dataCap: Cap @# ty) (exception: Pair Bool Data @# ty)
                             (isJal: bool) (changeIe: Bool @# ty) (ie: Bool @# ty) : FuncOutput @# ty :=
      STRUCT {
          "data"             ::= STRUCT {
                                     "tag" ::= dataTag;
                                     "cap" ::= dataCap;
                                     "val" ::= (IF exception @% "fst" then exception @% "snd" else dataVal) };
          "addrCapOrMemOp"   ::= addrCap;
          "addr"             ::= addrVal;
          "interruptOrBJal?" ::= $$isJal;
          "wb?"              ::= !(exception @% "fst");
          "pcUpd?"           ::= !(exception @% "fst");
          "mem?"             ::= $$false;
          "exception?"       ::= (exception @% "fst");
          "changeIe?"        ::= if isJal then $$false else !(exception @% "fst") && changeIe;
          "ie?"              ::= if isJal then $$false else ie }.

    Definition mkFenceI : FuncOutput @# ty :=
      STRUCT {
          "data"             ::= intResult $FenceI;
          "addrCapOrMemOp"   ::= addrCap;
          "addr"             ::= addrVal;
          "interruptOrBJal?" ::= $$true;
          "wb?"              ::= $$false;
          "pcUpd?"           ::= $$false;
          "mem?"             ::= $$false;
          "exception?"       ::= $$false;
          "changeIe?"        ::= $$false;
          "ie?"              ::= $$false }.

    Definition mkWfi : FuncOutput @# ty :=
      STRUCT {
          "data"             ::= intResult $Wfi;
          "addrCapOrMemOp"   ::= addrCap;
          "addr"             ::= addrVal;
          "interruptOrBJal?" ::= $$true;
          "wb?"              ::= $$false;
          "pcUpd?"           ::= $$false;
          "mem?"             ::= $$false;
          "exception?"       ::= $$false;
          "changeIe?"        ::= $$false;
          "ie?"              ::= $$false }.

    Definition mkLd (size: MemSize @# ty) (accessTag: Bool @# ty) (signExt: Bool @# ty) (perms: CapPerms @# ty)
                    (exception: Pair Bool Data @# ty): FuncOutput @# ty :=
      STRUCT {
          "data"             ::= intResult (IF exception @% "fst" then exception @% "snd" else dataVal);
          "addrCapOrMemOp"   ::= ZeroExtendTruncLsb CapSz
                                   (pack ((STRUCT {
                                               "memOp"      ::= $LdOp;
                                               "size"       ::= size;
                                               "signExt?"   ::= signExt;
                                               "MC"         ::= ITE accessTag (perms @% "MC") $$false;
                                               "LM"         ::= ITE accessTag (perms @% "LM") $$false;
                                               "LG"         ::= ITE accessTag (perms @% "LG") $$false;
                                               "accessTag?" ::= accessTag }): MemOpInfo @# ty));
          "addr"             ::= addrVal;
          "interruptOrBJal?" ::= $$false;
          "wb?"              ::= !(exception @% "fst");
          "pcUpd?"           ::= $$false;
          "mem?"             ::= $$true;
          "exception?"       ::= (exception @% "fst");
          "changeIe?"        ::= $$false;
          "ie?"              ::= $$false }.

    Definition mkSt (dataTag: Bool @# ty) (dataCap: Cap @# ty) (size: MemSize @# ty) (accessTag: Bool @# ty)
      (exception: Pair Bool Data @# ty) : FuncOutput @# ty :=
      STRUCT {
          "data"             ::= STRUCT {
                                     "tag" ::= dataTag;
                                     "cap" ::= dataCap;
                                     "val" ::= (IF exception @% "fst" then exception @% "snd" else dataVal) };
          "addrCapOrMemOp"   ::= ZeroExtendTruncLsb CapSz
                                   (pack ((STRUCT {
                                               "memOp"      ::= $StOp;
                                               "size"       ::= size;
                                               "signExt?"   ::= $$false;
                                               "MC"         ::= $$false;
                                               "LM"         ::= $$false;
                                               "LG"         ::= $$false;
                                               "accessTag?" ::= accessTag }): MemOpInfo @# ty));
          "addr"             ::= addrVal;
          "interruptOrBJal?" ::= $$false;
          "wb?"              ::= $$false;
          "pcUpd?"           ::= $$false;
          "mem?"             ::= $$true;
          "exception?"       ::= (exception @% "fst");
          "changeIe?"        ::= $$false;
          "ie?"              ::= $$false }.

  End FuncOutputHelpers.

  Record InstEntry ik ok :=
    { instName       : string;
      xlens          : list nat;
      extensions     : list Extension;
      uniqId         : UniqId;
      inputXform     : forall ty, FullCap @# ty -> Inst @# ty ->
                                  FullCapWithTag @# ty -> FullCapWithTag @# ty ->
                                  Bool @# ty -> ik ## ty;
      outputXform    : forall ty, ok @# ty -> FuncOutput ## ty;
      instProperties : InstProperties }.

  Record FuncEntry :=
    { funcName   : string;
      funcInput  : Kind;
      funcOutput : Kind;
      func       : forall ty, funcInput ## ty -> funcOutput ## ty;
      insts      : list (InstEntry funcInput funcOutput) }.
End ParamDefinitions.
