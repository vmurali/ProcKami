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
      getCapBase: forall ty, Bit CapSz @# ty -> Bit AddrSz @# ty -> Bit AddrSz ## ty;
      getCapTop: forall ty, Bit CapSz @# ty -> Bit AddrSz @# ty -> Bit (AddrSz + 1) ## ty;
      isSealed: forall ty, Bit CapSz @# ty -> Bool @# ty;
      isSentry: forall ty, Bit CapSz @# ty -> Bool @# ty;
      getPerms: forall ty, Bit CapSz @# ty -> CapPerms ## ty;
      seal: forall ty, Bit CapSz @# ty -> Bool @# ty -> Bit CapSz @# ty;
      unseal: forall ty, Bit CapSz @# ty -> Bit CapSz @# ty;
      isIeSentry: forall ty, Bit CapSz @# ty -> Bool @# ty;
      isIdSentry: forall ty, Bit CapSz @# ty -> Bool @# ty;
      setPerms: forall ty, Bit CapSz @# ty -> CapPerms @# ty -> Bit CapSz ## ty
    }.
End CapAccessors.

Inductive Extension := Base | M.

Definition PccValid Xlen CapSz (capAccessors: CapAccessors CapSz Xlen) (pcCap: word CapSz) (pcAddr: word Xlen)
  (compressed: bool) :=
  evalLetExpr ( LETE perms <- getPerms capAccessors (Const type pcCap);
                RetE (Var type (SyntaxKind CapPerms) perms @% "EX"))%kami_expr = true /\
    evalExpr ((isSealed capAccessors (Const _ pcCap))) = false /\
    if compressed then truncLsb pcAddr = ZToWord 2 0 else True.

(* Changes from CherIoT:
   - AUIPCC, AUICGP, CIncAddr and CSetAddr checks for bounds before clearing the tag
     instead of representability checks
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
      { hasRs1   : bool ;
        hasRs2   : bool ;
        implicit : nat }.
  End InstEncoding.

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
    destruct procParams as [_ xlen xlen_vars _ _ _ _ _ _ _ _ _ _ _].
    destruct xlen_vars; subst; simpl; lia.
  Qed.

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

(*
  Section Exception.
    (* Exception causes *)
    Definition MemAccess           := 4.  (* Addr *)
    Definition MemTranslationFault := 5.  (* Addr *)
    Definition MisalignedCap       := 6.  (* Addr *)
    Definition MisalignedData      := 7.  (* Addr *)

    Definition ExceptionCauseSz := 5.
    Definition ExceptionCause := Bit ExceptionCauseSz.
    Definition ExceptionValueSz := Nat.max Xlen RegIdSz.
    Definition ExceptionValue := Bit ExceptionValueSz.
    Definition Exception :=
      STRUCT_TYPE {
          "exceptionCause" :: ExceptionCause;
          "exceptionValue" :: ExceptionValue }.

    Section Ty.
      Variable ty: Kind -> Type.
      Local Open Scope kami_expr.
      
      Definition createRegException (r: RegId @# ty) (e: ExceptionCause @# ty) : Exception @# ty :=
        STRUCT {
            "exceptionCause" ::= e;
            "exceptionValue" ::= ZeroExtendTruncLsb ExceptionValueSz r
          }.

      Definition createAddrException (a: Addr @# ty) (e: ExceptionCause @# ty) : Exception @# ty :=
        STRUCT {
            "exceptionCause" ::= e;
            "exceptionValue" ::= ZeroExtendTruncLsb ExceptionValueSz a
          }.

      Section CarryK.
        Variable carry: string.
        Variable CarryK: Kind.
        
        Section K.
          Variable K : Kind.
          Definition Exceptionify :=
            STRUCT_TYPE {
                "data"       :: Bit (Nat.max (size K) (size Exception));
                "exception?" :: Bool;
                carry        :: CarryK
              }.
          
          Definition getException (val: Exceptionify @# ty) : Exception @# ty :=
            unpack _ (ZeroExtendTruncLsb (size Exception) (val @% "data")).

          Definition getNonException (val: Exceptionify @# ty) : K @# ty :=
            unpack _ (ZeroExtendTruncLsb (size K) (val @% "data")).
          
          Definition mkException (newCarry: CarryK @# ty) (e: Exception @# ty) : Exceptionify @# ty :=
            STRUCT {
                "data"       ::= ZeroExtendTruncLsb _ (pack e);
                "exception?" ::= $$ true;
                carry        ::= newCarry }.
          
          Definition mkNonException (newCarry: CarryK @# ty) (ne: K @# ty) : Exceptionify @# ty :=
            STRUCT {
                "data"       ::= ZeroExtendTruncLsb _ (pack ne);
                "exception?" ::= $$ false;
                carry        ::= newCarry }.
        End K.

        Definition bindExceptionify K1 K2 (v1: Exceptionify K1 @# ty)
          (f: K1 @# ty -> Exceptionify K2 @# ty): Exceptionify K2 @# ty :=
          IF v1 @% "exception?"
        then unpack _ (ZeroExtendTruncLsb _ (pack v1))
        else f (unpack K1 (ZeroExtendTruncLsb _ (v1 @% "data"))).
        
        Definition bindLetExceptionify K1 K2 (v1: Exceptionify K1 @# ty)
          (f: K1 @# ty -> Exceptionify K2 ## ty): Exceptionify K2 ## ty :=
          IfE v1 @% "exception?"
        then RetE (unpack _ (ZeroExtendTruncLsb _ (pack v1)))
        else f (unpack K1 (ZeroExtendTruncLsb _ (v1 @% "data"))) as v;
        RetE #v.
        
        Definition bindActionExceptionify K1 K2 (v1: Exceptionify K1 @# ty)
          (f: K1 @# ty -> ActionT ty (Exceptionify K2)): ActionT ty (Exceptionify K2) :=
          (If v1 @% "exception?"
           then Ret (unpack _ (ZeroExtendTruncLsb _ (pack v1)))
           else f (unpack K1 (ZeroExtendTruncLsb _ (v1 @% "data"))) as v;
           Ret #v)%kami_action.
      End CarryK.

      Definition ExceptionifyPcc := Exceptionify "pcc" FullCap.
      Definition mkExceptionPcc (pcc: FullCap @# ty) e K : ExceptionifyPcc K @# ty := @mkException "pcc" FullCap K pcc e.
      Definition mkNonExceptionPcc (pcc: FullCap @# ty) K ne : ExceptionifyPcc K @# ty := @mkNonException "pcc" FullCap K pcc ne.
      Definition ExceptionifyVoid := Exceptionify "dummy" Void.
      Definition mkExceptionVoid e K : ExceptionifyVoid K @# ty := @mkException "dummy" Void K ($$(getDefaultConst Void)) e.
      Definition mkNonExceptionVoid K ne : ExceptionifyVoid K @# ty := @mkNonException "dummy" Void K ($$(getDefaultConst Void)) ne.
    End Ty.
  End Exception.
  
  Definition EfiedFetchOutput := ExceptionifyPcc Inst.

  Definition EfiedFuncOutput := ExceptionifyVoid FuncOutput.
  
  Definition ExecOutput :=
    STRUCT_TYPE {
        "compressed?"    :: Bool;
        "regId"          :: RegId;
        "funcOutput"     :: EfiedFuncOutput }.

  Record FuncEntry :=
    { funcName    : string;
      inputK      : Kind;
      outputK     : Kind;
      func        : forall ty, inputK ## ty -> outputK ## ty;
      insts       : list (InstEntry inputK outputK) }.

  Definition MemOutput :=
    STRUCT_TYPE {
        "regWrite?" :: Bool;
        "regId"     :: RegId;
        "data"      :: FullCapWithTag;
        "nextPc"    :: FullCap;
        "fenceI?"   :: Bool }.

  Definition EfiedMemOutput := ExceptionifyPcc MemOutput.
End ParamDefinitions.
*)

(*
Section Params.
  Context {procParams: ProcParams}.
  
  Section DecoderHelpers.
    Variable ty: Kind -> Type.
    Variable n: nat.
    
    Definition inst_match_field
               (inst: Bit n @# ty)
               (field: FieldRange)
      := (LETE x <- extractArbitraryRange (RetE inst) (projT1 field);
            RetE (#x == $$ (projT2 field)))%kami_expr.

    Definition inst_match_id
               (inst: Bit n @# ty)
               (inst_id : UniqId)
      :  Bool ## ty
      := utila_expr_all (map (inst_match_field inst) inst_id).

    Definition inst_match_xlen
               (supp_xlens: list nat)
               (xlen : XlenValue @# ty)
      :  Bool ## ty
      := (RetE
            (utila_any
               (map
                  (fun supported_xlen => xlenFix xlen == $supported_xlen)
                  supp_xlens)))%kami_expr.

    Definition inst_match_enabled_exts
               (exts: list string)
               (exts_pkt : Extensions @# ty)
      :  Bool ## ty
      := utila_expr_any
           (map
              (fun ext : string
                 => RetE (struct_get_field_default exts_pkt ext $$false))
              exts)%kami_expr.
  End DecoderHelpers.
  
  Section ty.
    Variable ty: Kind -> Type.

    Local Open Scope kami_expr.
    Local Open Scope kami_action.

    Definition readSatpMode
      :  ActionT ty SatpMode
      := if hasVirtualMem
           then
             Read satp_mode : SatpMode <- @^"satp_mode";
             Ret #satp_mode
           else
             Ret ($SatpModeBare : SatpMode @# ty).

    Definition readSatpPpn
      :  ActionT ty SatpPpn
      := if hasVirtualMem
           then
             Read satp_ppn : SatpPpn <- @^"satp_ppn";
             Ret #satp_ppn
           else
             Ret ($0 : SatpPpn @# ty).


    Local Close Scope kami_action.
    Local Close Scope kami_expr.

    Definition LgPageSz := 12.

    (* virtual memory translation params.*)
    Record VmMode
      := { vm_mode_vpn_size: nat ;
           vm_mode_shift_num: nat ;
           vm_mode_sizes: list nat ;
           vm_mode_mode: word SatpModeWidth
         }.

    (* See 4.3.1 *)
    Definition vm_mode_sv32
      := {| vm_mode_vpn_size := 10 ;
            vm_mode_shift_num := 2 ;
            vm_mode_sizes := [12 ; 10 ];
            vm_mode_mode := $SatpModeSv32 |}.

    Definition vm_mode_sv39
      := {| vm_mode_vpn_size := 9 ;
            vm_mode_shift_num := 3 ;
            vm_mode_sizes := [26 ; 9; 9 ];
            vm_mode_mode := $SatpModeSv39 |}.

    Definition vm_mode_sv48
      := {| vm_mode_vpn_size := 9 ;
            vm_mode_shift_num := 4 ;
            vm_mode_sizes := [17 ; 9; 9; 9 ];
            vm_mode_mode := $SatpModeSv48 |}.

    Definition vmModes := [vm_mode_sv32; vm_mode_sv39; vm_mode_sv48].

    Definition vm_mode_max_vpn_size : nat
      := (fold_left
            (fun acc vm_mode => fold_left Nat.max (vm_mode_sizes vm_mode) acc)
            vmModes 0).

    Definition vm_mode_width vm_mode
      := (((vm_mode_vpn_size vm_mode) * (vm_mode_shift_num vm_mode)) + LgPageSz)%nat.

    Definition vm_mode_max_width
      := fold_left Nat.max (map vm_mode_width vmModes) 0.

    Definition vm_mode_max_field_size
      := fold_left Nat.max (map vm_mode_vpn_size vmModes) 0.

    Definition vm_mode_max_num_vpn_fields
      := fold_left Nat.max (map (fun mode => length (vm_mode_sizes mode)) vmModes) 0.

    Local Open Scope kami_expr.
    Definition faultException
               (access_type : AccessType @# ty)
      :  Exception @# ty
      := Switch access_type Retn Exception With {
                          ($VmAccessInst : AccessType @# ty)
                          ::= ($InstPageFault : Exception @# ty);
                          ($VmAccessLoad : AccessType @# ty)
                          ::= ($LoadPageFault : Exception @# ty);
                          ($VmAccessSAmo : AccessType @# ty)
                          ::= ($SAmoPageFault : Exception @# ty)
                        }.

    Definition accessException
               (access_type : AccessType @# ty)
      :  Exception @# ty
      := Switch access_type Retn Exception With {
                          ($VmAccessInst : AccessType @# ty)
                          ::= ($InstAccessFault : Exception @# ty);
                          ($VmAccessLoad : AccessType @# ty)
                          ::= ($LoadAccessFault : Exception @# ty);
                          ($VmAccessSAmo : AccessType @# ty)
                          ::= ($SAmoAccessFault : Exception @# ty)
                        }.

    Definition misalignedException
               (access_type : AccessType @# ty)
      :  Exception @# ty
      := Switch access_type Retn Exception With {
                          ($VmAccessInst : AccessType @# ty)
                          ::= ($InstAddrMisaligned : Exception @# ty);
                          ($VmAccessLoad : AccessType @# ty)
                          ::= ($LoadAddrMisaligned : Exception @# ty);
                          ($VmAccessSAmo : AccessType @# ty)
                          ::= ($SAmoAddrMisaligned : Exception @# ty)
                        }.

    Definition satp_select (satp_mode : SatpMode @# ty) k (f: VmMode -> k @# ty): k @# ty :=
      Switch satp_mode Retn k With {
        ($SatpModeSv32 : SatpMode @# ty)
          ::= f vm_mode_sv32;
        ($SatpModeSv39 : SatpMode @# ty)
          ::= f vm_mode_sv39;
        ($SatpModeSv48 : SatpMode @# ty)
          ::= f vm_mode_sv48
      }.


    Definition bindException
               (input_kind output_kind : Kind)
               (input : input_kind @# ty)
               (exception : Maybe Exception @# ty)
               (act : input_kind @# ty -> ActionT ty (PktWithException output_kind))
      :  ActionT ty (PktWithException output_kind)
      := (LETA newVal <- act input;
          LET new_exception: Maybe Exception <- IF (exception @% "valid") then exception else #newVal @% "snd";
          LET retVal : PktWithException output_kind <- (STRUCT { "fst" ::= #newVal @% "fst";
                                                                 "snd" ::= #new_exception });
          Ret #retVal)%kami_action.

    Definition noUpdPkt: ExecUpdPkt @# ty := $$(getDefaultConst ExecUpdPkt).

    Definition isAligned (addr: VAddr @# ty) (numZeros: MemRqLgSize @# ty) :=
      ((~(~($0) << numZeros)) .& ZeroExtendTruncLsb (MemRqSize-1) addr) == $0.

    Definition checkAligned (addr : VAddr @# ty) (size : MemRqLgSize @# ty)
      :  Bool @# ty
      := if allow_misaligned
           then $$true
           else isAligned addr size.


    Local Close Scope kami_expr.

    Definition CsrUpdateCodeWidth := 2.
    Definition CsrUpdateCodeNone := 0.
    Definition CsrUpdateCodeMCycle := 1.
    Definition CsrUpdateCodeMInstRet := 2.

    Definition MemUpdateCodeWidth := 2.
    Definition MemUpdateCodeNone := 0.
    Definition MemUpdateCodeTime := 1.
    Definition MemUpdateCodeTimeCmp := 2.

    Definition PmpCfg := STRUCT_TYPE {
                             "L" :: Bool ;
                             "reserved" :: Bit 2 ;
                             "A" :: Bit 2 ;
                             "X" :: Bool ;
                             "W" :: Bool ;
                             "R" :: Bool }.

    Definition pmp_reg_width : nat := if Nat.eqb Xlen_over_8 4 then 32 else 54.

    Definition MemErrorPkt
      := STRUCT_TYPE {
             "pmp"        :: Bool; (* request failed pmp check *)
             "width"      :: Bool; (* unsupported access width *)
             "pma"        :: Bool; (* failed device pma check *)
             "misaligned" :: Bool  (* address misaligned and misaligned access not supported by device *)
           }.

    Local Open Scope kami_expr.

    Definition mem_error (err_pkt : MemErrorPkt @# ty) : Bool @# ty
      := err_pkt @% "pmp" ||
         err_pkt @% "width" ||
         err_pkt @% "pma" ||
         err_pkt @% "misaligned".

    Definition getMemErrorException
      (access_type : AccessType @# ty)
      (err_pkt : MemErrorPkt @# ty)
      :  Exception @# ty
      := IF err_pkt @% "misaligned"
           then misalignedException access_type
           else accessException access_type.

    Section XlenInterface.

      (* warning: must be n <= m. *)
      Definition unsafeTruncLsb
                 (n m : nat)
                 (x : Bit n @# ty)
      :  Bit m @# ty
        := ZeroExtendTruncLsb m x.

      Definition extendTruncLsb
                 (f : forall n m : nat, Bit n @# ty -> Bit m @# ty)
                 (n m k : nat)
                 (x : Bit n @# ty)
        :  Bit k @# ty
        := f m k (@unsafeTruncLsb n m x).

      Definition zero_extend_trunc := extendTruncLsb (@ZeroExtendTruncLsb ty).

      Definition sign_extend_trunc := extendTruncLsb (@SignExtendTruncLsb ty).

      Definition one_extend_trunc := extendTruncLsb (@OneExtendTruncLsb ty).

      Definition extendMsbWithFunc
                 (f : forall n m : nat, Bit n @# ty -> Bit m @# ty)
                 (n m : nat)
                 (w : XlenValue @# ty)
                 (x : Bit n @# ty)
        :  Bit m @# ty
        := (IF w == $Xlen32
            then f 32 m (@unsafeTruncLsb n 32 x)
            else f 64 m (@unsafeTruncLsb n 64 x))%kami_expr.

      Definition xlen_trunc_msb := extendMsbWithFunc (@ZeroExtendTruncMsb ty).

      Definition xlen_zero_extend := extendMsbWithFunc (@ZeroExtendTruncLsb ty).

      Definition xlen_sign_extend := extendMsbWithFunc (@SignExtendTruncLsb ty).

      Definition flen_one_extend
                 (n m : nat)
        := @extendMsbWithFunc (@OneExtendTruncLsb ty) n m
                              (if Nat.eqb Flen_over_8 4
                               then $Xlen32
                               else $Xlen64)%kami_expr.
    End XlenInterface.
    
    Local Open Scope kami_expr.

    (* See 3.1.1 and 3.1.15 *)
    Definition maskEpc (exts : Extensions @# ty) (epc : VAddr @# ty)
      :  VAddr @# ty
      := let shiftAmount := (IF struct_get_field_default exts "C" ($$ false) then $1 else $2): Bit 2 @# ty in
         (epc >> shiftAmount) << shiftAmount.

    Local Close Scope kami_expr.

    Definition CsrFieldUpdGuard
      := STRUCT_TYPE {
             "warlUpdateInfo" :: WarlUpdateInfo;
             "cfg" :: ContextCfgPkt
           }.

    Record CompInstEntry
      := {
          comp_inst_xlens: list nat;
          req_exts: list string;
          comp_inst_id: UniqId;
          decompressFn: (CompInst @# ty) -> (Inst ## ty)
        }.

  End ty.

  Section func_units.
    Variable func_units : list FUEntry.

    (* instruction database ids. *)
    Definition FuncUnitIdWidth := Nat.log2_up (length func_units).

    Definition inst_max_num :=
      (fold_left
         (fun acc func_unit => max acc (length (fuInsts func_unit)))
         func_units
         0).

    Definition InstIdWidth := Nat.log2_up inst_max_num.
    Definition FuncUnitId : Kind := Bit FuncUnitIdWidth.
    Definition InstId : Kind := Bit InstIdWidth.

    (* Represents the kind of packets output by the decoder. *)
    Definition DecoderPkt := STRUCT_TYPE {
                                 "funcUnitTag" :: FuncUnitId;
                                 "instTag"     :: InstId;
                                 "inst"        :: Inst }.

    Definition FuncUnitInputWidth :=
      fold_left
        (fun acc func_unit => max acc (size (fuInputK func_unit)))
        func_units
        0.

    Definition FuncUnitInput :=
      Bit FuncUnitInputWidth.

    Definition InputTransPkt :=
      STRUCT_TYPE {
          "funcUnitTag" :: FuncUnitId;
          "instTag"     :: InstId;
          "inp"         :: FuncUnitInput
        }.

    Section ty.
      Variable ty : Kind -> Type.

      Local Open Scope kami_expr.

      (*
        Applies [f] to every instruction in the instruction database and
        returns the result for the instruction entry that satisfies [p].
      *)
      Definition inst_db_find_pkt
          (result_kind : Kind)
          (p : forall func_unit : FUEntry,
                 nat ->
                 (nat * InstEntry (fuInputK func_unit) (fuOutputK func_unit)) ->
                 Bool ## ty)
          (f : forall func_unit : FUEntry,
                 nat ->
                 (nat * InstEntry (fuInputK func_unit) (fuOutputK func_unit)) ->
                 result_kind ## ty)

        :  Maybe result_kind ## ty
        := utila_expr_find_pkt
             (map
                (fun tagged_func_unit : (nat * FUEntry)
                   => let (func_unit_id, func_unit)
                        := tagged_func_unit in
                      utila_expr_lookup_table
                        (tag (fuInsts func_unit))
                        (fun tagged_inst
                           => p func_unit
                                func_unit_id
                                tagged_inst)
                        (fun tagged_inst
                           => f func_unit
                                func_unit_id
                                tagged_inst))
                (tag func_units)).

      (*
        Applies [f] to every instruction in the instruction database and
        returns the result for the instruction referenced by [func_unit_id]
        and [inst_id].
      *)
      Definition inst_db_get_pkt
          (result_kind : Kind)
          (f : forall func_unit : FUEntry,
                 nat ->
                 (nat * InstEntry (fuInputK func_unit) (fuOutputK func_unit)) ->
                 result_kind ## ty)
          (sel_func_unit_id : FuncUnitId @# ty)
          (sel_inst_id : InstId @# ty)
        :  Maybe result_kind ## ty
        := inst_db_find_pkt
             (fun _ func_unit_id tagged_inst
                => RetE
                     (($(fst tagged_inst) == sel_inst_id) &&
                      ($(func_unit_id)    == sel_func_unit_id)))
             f.

      Definition applyInst
        (k : Kind)
        (f : forall t u : Kind, InstEntry t u -> k ## ty)
        (func_unit_id : FuncUnitId @# ty)
        (inst_id : InstId @# ty)
        :  k ## ty
        := LETE result
             :  Maybe k
             <- inst_db_get_pkt
                  (fun func_unit _ tagged_inst
                    => f (fuInputK func_unit)
                         (fuOutputK func_unit)
                         (snd tagged_inst))
                  func_unit_id
                  inst_id;
          RetE (#result @% "data").

      Local Open Scope kami_action.
    End ty.
  End func_units.

  Definition DebugCauseEBreak := 1.
  Definition DebugCauseHalt   := 3.
  Definition DebugCauseStep   := 4.
End Params.

*)
