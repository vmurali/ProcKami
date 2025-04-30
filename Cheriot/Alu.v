Require Import Kami.All.

Section CaseDefault.
  Variable ty: Kind -> Type.
  Variable k: Kind.
  Variable ls: list ((Bool @# ty) * (k @# ty)).
  Variable def: k @# ty.
  Definition caseDefault :=
    let allExprs := map (fun '(x, y) => ITE x y (Const ty Default)) ls in
    Kor (ITE (UniBool Neg (Kor (map fst ls))) def (Const ty Default) :: allExprs).
End CaseDefault.

Definition Xlen := 32.
Definition Data := Bit Xlen.
Definition AddrSz := Xlen.
Definition Addr := Bit AddrSz.
Definition LgAddrSz := Nat.log2_up AddrSz.
Definition ExpSz := LgAddrSz.
Definition CapExceptSz := 5.

Definition InstSz := 32.
Definition Inst := Bit 32.
Definition CompInstSz := 16.
Definition CompInst := Bit 16.
Definition HasComp := true.
Definition NumLsb0BitsInstAddr := Eval compute in (Nat.log2_up ((if HasComp then CompInstSz else InstSz)/8)).

Definition RegIdSz := 4.
Definition NumRegs := Eval compute in (Nat.pow 2 RegIdSz).
Definition RegFixedIdSz := 5.
Definition NumRegsFixed := Eval compute in (Nat.pow 2 RegFixedIdSz).

Definition Imm12Sz := 12.
Definition Imm20Sz := 20.
Definition DecImmSz := Eval compute in (S Imm20Sz).

Definition CapPermSz := 6.
Definition CapOTypeSz := 3.
Definition CapcMSz := 8.
Definition CapBSz := CapcMSz + 1.
Definition CapMSz := CapBSz.

Definition IeBit := 4. (* 4th bit counting from 0, i.e. mstatus[3] = IE *)

Section Exceptions.
  Definition BoundsViolation := 1.
  Definition TagViolation := 2.
  Definition SealViolation := 3.
  Definition ExViolation := 17.
  Definition LdViolation := 18.
  Definition SdViolation := 19.
  (* Note: Definition McLdViolation := 20. Clear loaded tag when Mc is absent *)
  Definition McSdViolation := 21.
  Definition SrViolation := 24.
  Definition IllegalException := 2.
  Definition EBreakException := 3.
  Definition LdAlignException := 4.
  Definition SdAlignException := 6.
  Definition ECallException := 11.
  Definition CapException := 28.

  Definition McauseSz := 5.
End Exceptions.

Section Interrupts.
  Definition Mei := 11.
  Definition Mti := 7.
End Interrupts.

Section Csr.
  (* TODO CSRs performance counters *)
  Definition Mcycle : N := hex "B00".
  Definition Mtime : N := hex "B01".
  Definition Minstret : N := hex "B02".
  Definition Mcycleh : N := hex "B80".
  Definition Mtimeh : N := hex "B81".
  Definition Minstreth : N := hex "B82".
  Definition Mshwm : N := hex "BC1".
  Definition Mshwmb : N := hex "BC2".

  Definition Mstatus : N := hex "300".
  Definition Mcause : N := hex "342".
  Definition Mtval : N := hex "343".

  Definition MshwmAlign := 4.
  Definition CsrIdSz := Imm12Sz.
  Definition CsrId := Bit CsrIdSz.
End Csr.

Section Scr.
  Definition Mtcc := 28.
  Definition Mtdc := 29.
  Definition Mscratchc := 30.
  Definition Mepcc := 31.
End Scr.

Definition Cap : Kind :=
  (STRUCT_TYPE {
       "R" :: Bool;
       "p" :: Array CapPermSz Bool;
       "oType" :: Bit CapOTypeSz;
       "cE" :: Bit ExpSz;
       "cM" :: Bit CapcMSz;
       "B" :: Bit CapBSz })%kami_expr.

Definition CapPerms := STRUCT_TYPE { "U0" :: Bool ;
                                     "SE" :: Bool ;
                                     "US" :: Bool ;
                                     "EX" :: Bool ;
                                     "SR" :: Bool ;
                                     "MC" :: Bool ;
                                     "LD" :: Bool ;
                                     "SL" :: Bool ;
                                     "LM" :: Bool ;
                                     "SD" :: Bool ;
                                     "LG" :: Bool ;
                                     "GL" :: Bool }.

Definition ECap := STRUCT_TYPE { "R"     :: Bool;
                                 "perms" :: CapPerms;
                                 "oType" :: Bit CapOTypeSz;
                                 "E"     :: Bit ExpSz;
                                 "top"   :: Bit (AddrSz + 1);
                                 "base"  :: Bit (AddrSz + 1) }.

Definition FullECapWithTag := STRUCT_TYPE { "tag" :: Bool;
                                            "ecap" :: ECap;
                                            "addr" :: Addr }.

Definition DXlen := Eval compute in Xlen + Xlen.
Definition MemSzSz := Eval compute in Nat.log2_up (Nat.log2_up (DXlen/8)).
Definition FullCapSz := Eval compute in Xlen + size Cap.
Definition NumBytesFullCapSz := Eval compute in (FullCapSz/8).
Definition LgNumBytesFullCapSz := Eval compute in lgCeil NumBytesFullCapSz.

Section Fields.
  Context {ty: Kind -> Type}.
  Variable inst: Bit InstSz @# ty.

  Local Open Scope kami_expr.

  Definition instSizeField := (0, 2).
  Definition opcodeField := (2, 5).
  Definition funct3Field := (12, 3).
  Definition funct7Field := (25, 7).
  Definition funct6Field := (26, 6).
  Definition immField := (20, Imm12Sz).
  Definition rs1Field := (15, RegIdSz).
  Definition rs2Field := (20, RegIdSz).
  Definition rdField := (7, RegIdSz).
  Definition rs1FixedField := (15, RegFixedIdSz).
  Definition rs2FixedField := (20, RegFixedIdSz).
  Definition rdFixedField := (7, RegFixedIdSz).
  Definition auiLuiField := (12, Imm20Sz).

  Notation extractFieldFromInst span := (extractFieldExpr InstSz inst (fst span) (snd span)).

  Definition instSize := extractFieldFromInst instSizeField.
  Definition opcode := extractFieldFromInst opcodeField.
  Definition funct3 := extractFieldFromInst funct3Field.
  Definition funct7 := extractFieldFromInst funct7Field.
  Definition funct6 := extractFieldFromInst funct6Field.
  Definition rs1 := extractFieldFromInst rs1Field.
  Definition rs2 := extractFieldFromInst rs2Field.
  Definition rd := extractFieldFromInst rdField.
  Definition rs1Fixed := extractFieldFromInst rs1FixedField.
  Definition rs2Fixed := extractFieldFromInst rs2FixedField.
  Definition rdFixed := extractFieldFromInst rdFixedField.
  Definition c0 := 0.
  Definition ra := 1.
  Definition sp := 2.

  (* TODO: These should be derived from encoder/decoder *)
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

  Definition isCompressed := isAllOnes (TruncLsbTo 2 _ inst).
End Fields.

Section Cap.
  Variable ty: Kind -> Type.
  Local Open Scope kami_expr.

  Section CapPerms.
    Definition decodePerms (rawPerms: Array CapPermSz Bool @# ty) : CapPerms @# ty :=
      (IF rawPerms ![4]
       then (IF rawPerms ![3]
             then (STRUCT {
                       "U0" ::= $$false;
                       "SE" ::= $$false;
                       "US" ::= $$false;
                       "EX" ::= $$false;
                       "SR" ::= $$false;
                       "MC" ::= $$true;
                       "LD" ::= $$true;
                       "SL" ::= rawPerms ![2];
                       "LM" ::= rawPerms ![1];
                       "SD" ::= $$true;
                       "LG" ::= rawPerms ![0];
                       "GL" ::= rawPerms ![5] })
             else (IF rawPerms ![2]
                   then (STRUCT {
                             "U0" ::= $$false;
                             "SE" ::= $$false;
                             "US" ::= $$false;
                             "EX" ::= $$false;
                             "SR" ::= $$false;
                             "MC" ::= $$true;
                             "LD" ::= $$true;
                             "SL" ::= $$false;
                             "LM" ::= rawPerms ![1];
                             "SD" ::= $$false;
                             "LG" ::= rawPerms ![0];
                             "GL" ::= rawPerms ![5] })
                   else (IF !(rawPerms ![1]) && !(rawPerms ![0])
                         then (STRUCT {
                                   "U0" ::= $$false;
                                   "SE" ::= $$false;
                                   "US" ::= $$false;
                                   "EX" ::= $$false;
                                   "SR" ::= $$false;
                                   "MC" ::= $$true;
                                   "LD" ::= $$false;
                                   "SL" ::= $$false;
                                   "LM" ::= $$false;
                                   "SD" ::= $$true;
                                   "LG" ::= $$false;
                                   "GL" ::= rawPerms ![5] })
                         else (STRUCT {
                                   "U0" ::= $$false;
                                   "SE" ::= $$false;
                                   "US" ::= $$false;
                                   "EX" ::= $$false;
                                   "SR" ::= $$false;
                                   "MC" ::= $$false;
                                   "LD" ::= rawPerms ![1];
                                   "SL" ::= $$false;
                                   "LM" ::= $$false;
                                   "SD" ::= rawPerms ![0];
                                   "LG" ::= $$false;
                                   "GL" ::= rawPerms ![5] }))))
       else (IF rawPerms ![3]
             then (STRUCT {
                       "U0" ::= $$false;
                       "SE" ::= $$false;
                       "US" ::= $$false;
                       "EX" ::= $$true;
                       "SR" ::= rawPerms ![2];
                       "MC" ::= $$true;
                       "LD" ::= $$true;
                       "SL" ::= $$false;
                       "LM" ::= rawPerms ![1];
                       "SD" ::= $$false;
                       "LG" ::= rawPerms ![0];
                       "GL" ::= rawPerms ![5] })
             else (STRUCT {
                       "U0" ::= rawPerms ![2];
                       "SE" ::= rawPerms ![1];
                       "US" ::= rawPerms ![0];
                       "EX" ::= $$false;
                       "SR" ::= $$false;
                       "MC" ::= $$false;
                       "LD" ::= $$false;
                       "SL" ::= $$false;
                       "LM" ::= $$false;
                       "SD" ::= $$false;
                       "LG" ::= $$false;
                       "GL" ::= rawPerms ![5] }))).

    Definition fixPerms (perms: CapPerms @# ty) : CapPerms @# ty :=
      (IF perms @% "EX" && perms @% "LD" && perms @% "MC"
       then (STRUCT {
                 "U0" ::= $$false;
                 "SE" ::= $$false;
                 "US" ::= $$false;
                 "EX" ::= $$true;
                 "SR" ::= perms @% "SR";
                 "MC" ::= $$true;
                 "LD" ::= $$true;
                 "SL" ::= $$false;
                 "LM" ::= perms @% "LM";
                 "SD" ::= $$false;
                 "LG" ::= perms @% "LG";
                 "GL" ::= perms @% "GL" })
       else (IF perms @% "LD" && perms @% "MC" && perms @% "SD"
             then (STRUCT {
                       "U0" ::= $$false;
                       "SE" ::= $$false;
                       "US" ::= $$false;
                       "EX" ::= $$false;
                       "SR" ::= $$false;
                       "MC" ::= $$true;
                       "LD" ::= $$true;
                       "SL" ::= perms @% "SL";
                       "LM" ::= perms @% "LM";
                       "SD" ::= $$true;
                       "LG" ::= perms @% "LG";
                       "GL" ::= perms @% "GL" })
             else (IF perms @% "LD" && perms @% "MC"
                   then (STRUCT {
                             "U0" ::= $$false;
                             "SE" ::= $$false;
                             "US" ::= $$false;
                             "EX" ::= $$false;
                             "SR" ::= $$false;
                             "MC" ::= $$true;
                             "LD" ::= $$true;
                             "SL" ::= $$false;
                             "LM" ::= perms @% "LM";
                             "SD" ::= $$false;
                             "LG" ::= perms @% "LG";
                             "GL" ::= perms @% "GL" })
                   else (IF perms @% "SD" && perms @% "MC"
                         then (STRUCT {
                                   "U0" ::= $$false;
                                   "SE" ::= $$false;
                                   "US" ::= $$false;
                                   "EX" ::= $$false;
                                   "SR" ::= $$false;
                                   "MC" ::= $$true;
                                   "LD" ::= $$false;
                                   "SL" ::= $$false;
                                   "LM" ::= $$false;
                                   "SD" ::= $$true;
                                   "LG" ::= $$false;
                                   "GL" ::= perms @% "GL" })
                         else (IF perms @% "LD" || perms @% "SD"
                               then (STRUCT {
                                         "U0" ::= $$false;
                                         "SE" ::= $$false;
                                         "US" ::= $$false;
                                         "EX" ::= $$false;
                                         "SR" ::= $$false;
                                         "MC" ::= $$false;
                                         "LD" ::= perms @% "LD";
                                         "SL" ::= $$false;
                                         "LM" ::= $$false;
                                         "SD" ::= perms @% "SD";
                                         "LG" ::= $$false;
                                         "GL" ::= perms @% "GL" })
                               else (STRUCT {
                                         "U0" ::= perms @% "U0";
                                         "SE" ::= perms @% "SE";
                                         "US" ::= perms @% "US";
                                         "EX" ::= $$false;
                                         "SR" ::= $$false;
                                         "MC" ::= $$false;
                                         "LD" ::= $$false;
                                         "SL" ::= $$false;
                                         "LM" ::= $$false;
                                         "SD" ::= $$false;
                                         "LG" ::= $$false;
                                         "GL" ::= perms @% "GL" })))))).

    Definition encodePerms (perms: CapPerms @# ty) : Array CapPermSz Bool @# ty :=
      unpack (Array CapPermSz Bool)
        ({< pack (perms @% "GL"),
            ( IF perms @% "EX" && perms @% "LD" && perms @% "MC"
              then {< Const ty (2'b"01"), pack (perms @% "SR"), pack (perms @% "LM"), pack (perms @% "LG") >}
              else (IF perms @% "LD" && perms @% "MC" && perms @% "SD"
                    then {< Const ty (2'b"11"), pack (perms @% "SL"), pack (perms @% "LM"), pack (perms @% "LG") >}
                    else (IF perms @% "LD" && perms @% "MC"
                          then {< Const ty (3'b"101"), pack (perms @% "LM"), pack (perms @% "LG") >}
                          else (IF perms @% "SD" && perms @% "MC"
                                then Const ty (5'b"10000")
                                else (IF perms @% "LD" || perms @% "SD"
                                      then {< Const ty (3'b"100"), pack (perms @% "LD"), pack (perms @% "SD") >}
                                      else {< Const ty (2'b"00"), pack (perms @% "U0"), pack (perms @% "SE"),
                                         pack (perms @% "US") >})))))%kami_expr >}).
  End CapPerms.

  Section Sealed.
    Definition unsealed : Bit CapOTypeSz @# ty := $0.
    Section testOType.
      Variable otype: Bit CapOTypeSz @# ty.
      Definition isSealed := isNotZero otype.
      Definition isNotSealed := isZero otype.
      Definition isForwardSentry := Kor [otype == $1; otype == $2; otype == $3].
      Definition isBackwardSentry := otype == $4 || otype == $5.
      Definition isInterruptEnabling := otype == $3 || otype == $5.
      Definition isInterruptDisabling := otype == $2 || otype == $4.
      Definition isInterruptInheriting := otype == $1.
    End testOType.

    Section testAddr.
      Variable isExec: Bool @# ty.
      Variable addr: Addr @# ty.
      Definition isSealableAddr :=
        isZero (TruncMsbTo (AddrSz - CapOTypeSz) CapOTypeSz addr) &&
          TruncMsbTo 1 (CapOTypeSz - 1) (TruncLsbTo CapOTypeSz (AddrSz - CapOTypeSz) addr) != pack isExec.
    End testAddr.

    Definition createBackwardSentry (ie: Bool @# ty) : Bit CapOTypeSz @# ty := {< $$(2'b"10"), pack ie >}.
    Definition createForwardSentry (change ie: Bool @# ty): Bit CapOTypeSz @# ty :=
      {< $$WO~0, pack change, pack ie >}.
  End Sealed.

  Section CapRelated.
    Definition get_E_from_cE (cE: Bit ExpSz @# ty) : Bit ExpSz @# ty := ITE (isAllOnes cE) $0 cE.
    Definition get_Mmsb_from_cE (cE: Bit ExpSz @# ty) : Bit 1 @# ty := pack (isNotZero cE).
    Definition get_M_from_cE_cM (cE: Bit ExpSz @# ty) (cM: Bit CapcMSz @# ty) : Bit CapMSz @# ty :=
      ({< get_Mmsb_from_cE cE, cM >}).

    Definition get_Mmsb_from_M (M: Bit CapMSz @# ty) := TruncMsbTo 1 CapcMSz M.
    Definition get_cM_from_M (M: Bit CapMSz @# ty) := TruncLsbTo CapcMSz 1 M.
    Definition get_cE_from_E_M (E: Bit ExpSz @# ty) (M: Bit CapMSz @# ty) :=
      ITE (isZero E && unpack Bool (get_Mmsb_from_M M)) ($$(wones ExpSz)) E.
    Definition Emax := (Nat.pow 2 ExpSz - CapcMSz)%nat.
    Definition get_ECorrected_from_E (E: Bit ExpSz @# ty) : Bit ExpSz @# ty :=
      (ITE (E >= $Emax) $Emax E).
    Definition get_E_from_ECorrected (ECorrected: Bit ExpSz @# ty): Bit ExpSz @# ty := ECorrected.
  End CapRelated.

  Section Representable.
    Variable base: Bit (AddrSz + 1) @# ty.
    Variable ECorrected: Bit ExpSz @# ty.

    Definition getRepresentableLimit := base + {< ($1 << ECorrected), $$(wzero CapMSz) >}.
  End Representable.

  Section BaseLength.
    Definition BaseLength :=
      STRUCT_TYPE {
          "base"   :: Bit (AddrSz + 1);
          "length" :: Bit (AddrSz + 1) }.
    
    Variable addr: Addr @# ty.
    Variable ECorrected: Bit ExpSz @# ty.
    Variable M: Bit CapMSz @# ty.
    Variable B: Bit CapBSz @# ty.

    Definition get_base_length_from_ECorrected_M_B : BaseLength ## ty :=
      ( LETC aMidTop: Addr <- addr >> ECorrected;
        LETC aMid: Bit CapBSz <- TruncLsbTo CapBSz (AddrSz - CapBSz) #aMidTop;
        LETC aTop: Bit (AddrSz - CapBSz) <- TruncMsbTo (AddrSz - CapBSz) CapBSz #aMidTop;
        LETC aHi: Bit (AddrSz - CapBSz) <- ZeroExtendTo (AddrSz - CapBSz) (pack (#aMid < B));
        LETC base: Bit (AddrSz + 1) <- (ZeroExtendTo (AddrSz + 1) ({< #aTop - #aHi, B >})) << ECorrected;
        LETC length: Bit (AddrSz + 1) <- (ZeroExtendTo (AddrSz + 1) M) << ECorrected;
        LETC ret: BaseLength <- (STRUCT {
                                     "base"   ::= #base;
                                     "length" ::= #length });
        RetE #ret).
  End BaseLength.

  Section CalculateBounds.
    Variable base: Bit (AddrSz + 1) @# ty.
    Variable length: Bit (AddrSz + 1) @# ty.
    Variable IsSubset: Bool @# ty.
    Variable IsFixedBase: Bool @# ty.

    Local Notation shift_m_e sm m e :=
      (ITE (unpack Bool (TruncMsbTo 1 sm m))
         (mkPair ((ZeroExtend 1 (TruncMsbTo sm 1 m)) + ZeroExtend sm (TruncLsbTo 1 sm m)) (e+$1))
         (mkPair m e)).

    Local Notation shift_m_e_twice sm m e :=
      (LETC me: Pair (Bit (sm + 1)) (Bit ExpSz) <- shift_m_e sm m e;
       LETC m1e1: Pair (Bit (sm + 1)) (Bit ExpSz) <- shift_m_e sm (#me @% "fst") (#me @% "snd");
       RetE (STRUCT {
                 "fst" ::= (TruncLsbTo sm 1 (#m1e1 @% "fst"));
                 "snd" ::= (#m1e1 @% "snd") } : Pair (Bit sm) (Bit ExpSz) @# ty)).

    Definition Bounds :=
      STRUCT_TYPE {
          "E" :: Bit ExpSz;
          "cram" :: Bit (AddrSz + 1);
          "base" :: Bit (AddrSz + 1);
          "length" :: Bit (AddrSz + 1);
          "exact" :: Bool }.

    (* TODO check when length = 2^32-1 and base = 2^32-1 *)

    Definition calculateBounds : Bounds ## ty :=
      ( LETC lenTrunc : Bit (AddrSz + 1 - CapBSz) <- TruncMsbTo (AddrSz + 1 - CapBSz) CapBSz length;
        LETC eInit: Bit ExpSz <- $(AddrSz + 1 - CapBSz) + ~(countLeadingZeros _ #lenTrunc);
        LETC e_lgCeilAdd1: Bool <- (isNotZero (TruncLsbTo CapBSz (AddrSz + 1 - CapBSz) length) ||
                                      (countOnes ExpSz #lenTrunc != $1));
        LETC eLength: Bit ExpSz <-
                        #eInit + ZeroExtendTo ExpSz (pack (ITE IsSubset (isZero #lenTrunc) #e_lgCeilAdd1));
        LETC eBaseUncorrected : Bit (Nat.log2_up (AddrSz + 1)) <- countTrailingZeros _ base;
        LETC eBase <- TruncLsbTo ExpSz 1 (ITE (#eBaseUncorrected >= $Emax) $Emax #eBaseUncorrected);
        LETC fixedBase_eBase_lt_eLength <- IsFixedBase && (#eBase < #eLength);
        LETC e <- ITE #fixedBase_eBase_lt_eLength #eBase #eLength;
        LETC mask_e : Bit (AddrSz + 2 - CapBSz) <- ~ ($$(wones (AddrSz + 2 - CapBSz)) << #e);
        LETC base_mod_e : Bit (AddrSz + 2 - CapBSz) <- (TruncLsbTo (AddrSz + 2 - CapBSz) _ base) .& #mask_e;
        LETC length_mod_e : Bit (AddrSz + 2 - CapBSz) <- (TruncLsbTo (AddrSz + 2 - CapBSz) _ length) .& #mask_e;
        LETC sum_mod_e : Bit (AddrSz + 2 - CapBSz) <- #base_mod_e + #length_mod_e;
        LETC iFloor : Bit 2 <- TruncLsbTo 2 _ (#sum_mod_e >> #e);
        LETC lost_sum : Bool <- isNotZero (#sum_mod_e .& #mask_e);
        LETC iCeil : Bit 2 <- #iFloor + ZeroExtendTo 2 (pack #lost_sum);
        LETC d : Bit (CapBSz + 2) <- TruncLsbTo (CapBSz + 2) _ (length >> #e);
        LETC m : Bit (CapBSz + 2) <- (ITE #fixedBase_eBase_lt_eLength $(Nat.pow 2 CapMSz - 1) #d) +
                                       ZeroExtend CapBSz (ITE IsSubset $0 #iCeil);
        LETE m1e1: Pair (Bit (CapBSz + 1)) (Bit ExpSz) <- shift_m_e_twice (CapBSz + 1) #m #e;
        LETE m2e2: Pair (Bit CapBSz) (Bit ExpSz) <- shift_m_e_twice CapBSz (#m1e1 @% "fst") (#m1e1 @% "snd");
        LETC mf: Bit CapBSz <- #m2e2 @% "fst";
        LETC efUnsat: Bit ExpSz <- #m2e2 @% "snd";
        LETC isESaturated: Bool <- #efUnsat > $(AddrSz + 1 - CapBSz);
        LETC ef <- ITE #isESaturated $(AddrSz + 1 - CapBSz) #efUnsat;
        LETC cram : Bit (AddrSz + 1) <- $$(wones (AddrSz + 1)) << #ef;
        LETC mask_ef : Bit (AddrSz + 1) <- ~#cram;
        LETC lost_base : Bool <- isNotZero (base .& #mask_ef);
        LETC outBase <-  (base .& #cram);
        (* TODO for subset without fixed base.
           + (ZeroExtend Xlen (pack (IsSubset && #lost_base &&
           !(#isESaturated && ((base .& #cram) == #cram))))) << #ef *)
        LETC outLength: Bit (AddrSz + 1) <- (ZeroExtendTo (AddrSz + 1) #mf) << #ef;
        LETC ret: Bounds <- STRUCT {
                                "E" ::= #ef;
                                "cram" ::= #cram;
                                "base" ::= #outBase;
                                "length" ::= #outLength;
                                "exact" ::= (#lost_base || (length != #outLength)) };
        RetE #ret
      ).
  End CalculateBounds.

  Section EncodeCap.
    Variable ecap: ECap @# ty.

    Definition encodeCap: Cap ##ty :=
      ( LETC perms <- encodePerms (ecap @% "perms");
        LETC E <- ecap @% "E";
        LETC ECorrected <- get_ECorrected_from_E #E;
        LETC B <- TruncLsbTo CapBSz (AddrSz + 1 - CapBSz) ((ecap @% "base") >> #ECorrected);
        LETC T <- TruncLsbTo CapBSz (AddrSz + 1 - CapBSz) ((ecap @% "top") >> #ECorrected);
        LETC M <- #T - #B;
        LETC ret: Cap <- STRUCT {
                             "R" ::= ecap @% "R";
                             "p" ::= #perms;
                             "oType" ::= ecap @% "oType";
                             "cE" ::= get_cE_from_E_M #E #M;
                             "cM" ::= get_cM_from_M #M;
                             "B" ::= #B };
        RetE #ret ).        
  End EncodeCap.

  Section DecodeCap.
    Variable cap: Cap @# ty.
    Variable addr: Addr @# ty.

    Definition decodeCap: ECap ##ty :=
      ( LETC perms <- decodePerms (cap @% "p");
        LETC E <- get_E_from_cE (cap @% "cE");
        LETC ECorrected <- get_ECorrected_from_E #E;
        LETE base_length <- get_base_length_from_ECorrected_M_B addr #ECorrected
                              (get_M_from_cE_cM (cap @% "cE") (cap @% "cM")) (cap @% "B");
        LETC base <- #base_length @% "base";
        LETC length <- #base_length @% "length";
        LETC ret: ECap <- STRUCT {
                             "R" ::= cap @% "R";
                             "perms" ::= #perms;
                             "oType" ::= cap @% "oType";
                             "E" ::= #E;
                             "top" ::= (#base + #length);
                             "base" ::= #base };
        RetE #ret ).
  End DecodeCap.
End Cap.

Definition Csrs := STRUCT_TYPE { "mcycle" :: Bit DXlen ;
                                  "mtime" :: Bit DXlen ;
                               "minstret" :: Bit DXlen ;
                                  "mshwm" :: Bit (Xlen - MshwmAlign) ;
                                 "mshwmb" :: Bit (Xlen - MshwmAlign) ;
                                  
                                     "ie" :: Bool ;
                              "interrupt" :: Bool ;
                                 "mcause" :: Bit McauseSz ;
                                  "mtval" :: Addr }.

Definition Scrs := STRUCT_TYPE {   "mtcc" :: FullECapWithTag ;
                                   "mtdc" :: FullECapWithTag ;
                              "mscratchc" :: FullECapWithTag ;
                                 "mepcc" :: FullECapWithTag }.

Definition Interrupts := STRUCT_TYPE { "mei" :: Bool ;
                                       "mti" :: Bool }.

Definition PcAluOut :=
  STRUCT_TYPE { "pcVal" :: Addr ;
      "BoundsException" :: Bool }.

Definition DecodeOut :=
  STRUCT_TYPE { "rs1Idx" :: Bit RegFixedIdSz;
                "rs2Idx" :: Bit RegFixedIdSz;
                 "rdIdx" :: Bit RegFixedIdSz;
                "decImm" :: Bit DecImmSz ;
                 "memSz" :: Bit MemSzSz ;

            "Compressed" :: Bool ;

           "ImmExtRight" :: Bool ;
            "ImmForData" :: Bool ;
            "ImmForAddr" :: Bool ;
 
              "ReadReg1" :: Bool ;
              "ReadReg2" :: Bool ;
              "WriteReg" :: Bool ;
 
            "MultiCycle" :: Bool ;
 
                "Src1Pc" :: Bool ;
               "InvSrc2" :: Bool ;
              "Src2Zero" :: Bool ;
                                  
                                  
        "ZeroExtendSrc1" :: Bool ;
                                  
                "Branch" :: Bool ;
              "BranchLt" :: Bool ;
             "BranchNeg" :: Bool ;
                   "Slt" :: Bool ;
                   "Add" :: Bool ;
                   "Xor" :: Bool ;
                    "Or" :: Bool ;
                                  
                                  
                   "And" :: Bool ;
                    "Sl" :: Bool ;
                    "Sr" :: Bool ;
                 "Store" :: Bool ;
                  "Load" :: Bool ;
          "LoadUnsigned" :: Bool ;
             "SetBounds" :: Bool ;
        "SetBoundsExact" :: Bool ;
          "BoundsSubset" :: Bool ;
       "BoundsFixedBase" :: Bool ;
   
           "CChangeAddr" :: Bool ;
                "AuiPcc" :: Bool ;
              "CGetBase" :: Bool ;
               "CGetTop" :: Bool ;
               "CGetLen" :: Bool ;
              "CGetPerm" :: Bool ;
              "CGetType" :: Bool ;
               "CGetTag" :: Bool ;
              "CGetHigh" :: Bool ;
                  "Cram" :: Bool ;
                  "Crrl" :: Bool ;
             "CSetEqual" :: Bool ;
           "CTestSubset" :: Bool ;
              "CAndPerm" :: Bool ;
             "CClearTag" :: Bool ;
              "CSetHigh" :: Bool ;
                 "CMove" :: Bool ;
                 "CSeal" :: Bool ;
               "CUnseal" :: Bool ;
     
                  "CJal" :: Bool ;
                 "CJalr" :: Bool ;
                "AuiAll" :: Bool ;
                   "Lui" :: Bool ;
   
            "CSpecialRw" :: Bool ;
                  "MRet" :: Bool ;
                 "ECall" :: Bool ;
                "EBreak" :: Bool ;
                "FenceI" :: Bool ;
                 "Fence" :: Bool ;
            "NotIllegal" :: Bool ;
   
                 "CsrRw" :: Bool ;
                "CsrSet" :: Bool ;
              "CsrClear" :: Bool ;
                "CsrImm" :: Bool }.

Definition AluIn :=
  STRUCT_TYPE {
             "pcAluOut" :: PcAluOut ;
                 "inst" :: Inst ;
            "decodeOut" :: DecodeOut ;
                 "reg1" :: FullECapWithTag ;
                 "reg2" :: FullECapWithTag ;
                 "regs" :: Array NumRegs FullECapWithTag ;
                "waits" :: Array NumRegs Bool ;
                 "csrs" :: Csrs ;
                 "scrs" :: Scrs ;
           "interrupts" :: Interrupts ;
             "incoming" :: Interrupts }.

Definition AluOut := STRUCT_TYPE { "regs" :: Array NumRegs FullECapWithTag ;
                                   "waits" :: Array NumRegs Bool ;
                                   "csrs" :: Csrs ;
                                   "scrs" :: Scrs ;
                                   "interrupts" :: Interrupts ;
                                   "ldRegIdx" :: Bit RegIdSz ;
                                   "memAddr" :: Addr ;
                                   "storeVal" :: FullECapWithTag ;
                                   "exception" :: Bool ; (* Note: For Branch Predictor *)
                                   "MRet" :: Bool ; (* Note: For Branch Predictor *)
                                   "Branch" :: Bool ; (* Note: For Branch Predictor *)
                                   "CJal" :: Bool ; (* Note: For Branch Predictor *)
                                   "CJalr" :: Bool ; (* Note: For Branch Predictor *)
                                   "LoadUnsigned" :: Bool ;
                                   "memSz" :: Bit MemSzSz ;
                                   "pcNotLinkAddrTagVal" :: Bool ;
                                   "pcNotLinkAddrCap" :: Bool ;
                                   "stall" :: Bool ;
                                   "Load" :: Bool ;
                                   "Store" :: Bool ;
                                   "FenceI" :: Bool }.

Section Decode.
  Variable ty: Kind -> Type.

  Local Notation ITE0 x y := (ITE x y (Const ty Default)).

  Variable inst: Inst @# ty.

  Local Open Scope kami_expr.

  Definition decodeFullInst: DecodeOut ## ty :=
    ( LETC op: Bit 5 <- opcode inst;
      LETC f3: Bit 3 <- funct3 inst;
      LETC f7: Bit 7 <- funct7 inst;
      LETC f6: Bit 6 <- funct6 inst;
      LETC rdIdx: Bit RegFixedIdSz <- rdFixed inst;
      LETC rs1Idx: Bit RegFixedIdSz <- rs1Fixed inst;
      LETC rs2Idx: Bit RegFixedIdSz <- rs2Fixed inst;
      LETC immVal: Bit (snd immField) <- imm inst;

      LETC Lui: Bool <- #op == $$(5'b"01101");
      LETC AuiPcc: Bool <- #op == $$(5'b"00101");
      LETC AuiCgp: Bool <- #op == $$(5'b"11110");
      LETC CJal: Bool <- #op == $$(5'b"11011");
      LETC CJalr: Bool <- #op == $$(5'b"11001") && isZero #f3;
      LETC Branch: Bool <- #op == $$(5'b"11000") && (#f3$[2:1] != $$(2'b"01"));

      LETC BranchLt: Bool <- unpack Bool (#f3$[2:2]);
      LETC BranchNeg: Bool <- unpack Bool (#f3$[0:0]);
      LETC BranchUnsigned: Bool <- unpack Bool (#f3$[1:1]);

      LETC Load: Bool <- isZero #op && !(isAllOnes #f3);
      LETC Store: Bool <- #op == $$(5'b"01000") && !(unpack Bool (#f3$[2:2]));

      LETC LoadUnsigned: Bool <- unpack Bool (#f3$[2:2]);
      LETC memSz: Bit MemSzSz <- #f3$[1:0];

      LETC immediate: Bool <- #op == $$(5'b"00100");
      LETC nonImmediate: Bool <- #op == $$(5'b"01100");
      LETC addF3: Bool <- #f3 == $0;
      LETC sllF3: Bool <- #f3 == $1;
      LETC sltF3: Bool <- #f3 == $2;
      LETC sltuF3: Bool <- #f3 == $3;
      LETC xorF3: Bool <- #f3 == $4;
      LETC srF3: Bool <- #f3 == $5;
      LETC orF3: Bool <- #f3 == $6;
      LETC andF3: Bool <- #f3 == $7;
      LETC slF7: Bool <- isZero #f7;
      LETC sraSubF7: Bool <- #f7 == $$(7'b"0100000");
      LETC nonImmF7: Bool <- isZero #f7;

      LETC AddI: Bool <- #immediate && #addF3;
      LETC SltI: Bool <- #immediate && #sltF3;
      LETC SltuI: Bool <- #immediate && #sltuF3;
      LETC XorI: Bool <- #immediate && #xorF3;
      LETC OrI: Bool <- #immediate && #orF3;
      LETC AndI: Bool <- #immediate && #andF3;
      LETC SllI: Bool <- #immediate && #sllF3 && #slF7;
      LETC SrlI: Bool <- #immediate && #srF3 && #slF7;
      LETC SraI: Bool <- #immediate && #srF3 && #sraSubF7;

      LETC Add: Bool <- #nonImmediate && #addF3 && #nonImmF7;
      LETC Sub: Bool <- #nonImmediate && #addF3 && #sraSubF7;
      LETC Sll: Bool <- #nonImmediate && #sllF3 && #nonImmF7;
      LETC Slt: Bool <- #nonImmediate && #sltF3 && #nonImmF7;
      LETC Sltu: Bool <- #nonImmediate && #sltuF3 && #nonImmF7;
      LETC Xor: Bool <- #nonImmediate && #xorF3 && #nonImmF7;
      LETC Srl: Bool <- #nonImmediate && #srF3 && #nonImmF7;
      LETC Sra: Bool <- #nonImmediate && #srF3 && #sraSubF7;
      LETC Or: Bool <- #nonImmediate && #orF3 && #nonImmF7;
      LETC And: Bool <- #nonImmediate && #andF3 && #nonImmF7;

      LETC isFence: Bool <- #op == $$(5'b"00011");

      LETC Fence: Bool <- #isFence && isZero #f3;
      LETC FenceI: Bool <- #isFence && #f3 == $1;

      LETC isSys: Bool <- #op == $$(5'b"11100");

      LETC eHandle: Bool <- #isSys && isZero #f3 && isZero #rdIdx && isZero #rs1Idx;
      LETC ECall: Bool <- #eHandle && isZero #f7 && isZero #rs2Idx;
      LETC Wfi: Bool <- #eHandle && #f7 == $$(7'b"0001000") && #rs2Idx == $$(5'b"00101");
      LETC EBreak: Bool <- #eHandle && isZero #f7 && #rs2Idx == $1;
      LETC MRet: Bool <- #eHandle && #f7 == $$(7'b"0011000") && #rs2Idx == $$(5'b"00010");

      LETC CsrRw: Bool <- #isSys && (#f3$[1:0]) == $1;
      LETC CsrSet: Bool <- #isSys && (#f3$[1:0]) == $2;
      LETC CsrClear: Bool <- #isSys && (#f3$[1:0]) == $3;

      LETC CsrImm: Bool <- #isSys && unpack Bool (#f3$[2:2]);

      LETC cheriot: Bool <- #op == $$(5'b"10110");
      LETC cheriotNonImm: Bool <- #cheriot && isZero #f3;
      LETC cheriot1Src: Bool <- #cheriotNonImm && #f7 == $$(7'h"7f");

      LETC CGetPerm: Bool <- #cheriot1Src && #rs2Idx == $0;
      LETC CGetType: Bool <- #cheriot1Src && #rs2Idx == $1;
      LETC CGetBase: Bool <- #cheriot1Src && #rs2Idx == $2;
      LETC CGetLen: Bool <- #cheriot1Src && #rs2Idx == $3;
      LETC CGetTag: Bool <- #cheriot1Src && #rs2Idx == $4;
      LETC CGetAddr: Bool <- #cheriot1Src && #rs2Idx == $$(5'h"f");
      LETC CGetHigh: Bool <- #cheriot1Src && #rs2Idx == $$(5'h"17");
      LETC CGetTop: Bool <- #cheriot1Src && #rs2Idx == $$(5'h"18");

      LETC CSeal: Bool <- #cheriotNonImm && #f7 == $$(7'h"b");
      LETC CUnseal: Bool <- #cheriotNonImm && #f7 == $$(7'h"c");
      LETC CAndPerm: Bool <- #cheriotNonImm && #f7 == $$(7'h"d");
      
      LETC CSetAddr: Bool <- #cheriotNonImm && #f7 == $$(7'h"10");
      LETC CIncAddr: Bool <- #cheriotNonImm && #f7 == $$(7'h"11");
      LETC CIncAddrImm: Bool <- #cheriot && #f3 == $1;
      
      LETC CSetBounds: Bool <- #cheriotNonImm && #f7 == $$(7'h"8");
      LETC CSetBoundsExact: Bool <- #cheriotNonImm && #f7 == $$(7'h"9");
      LETC CSetBoundsRoundDown: Bool <- #cheriotNonImm && #f7 == $$(7'h"a");
      LETC CSetBoundsImm: Bool <- #cheriot && #f3 == $2 && #f7 == $$(7'h"8");

      LETC CSetHigh: Bool <- #cheriotNonImm && #f7 == $$(7'h"16");
      LETC CClearTag: Bool <- #cheriot1Src && #rs2Idx == $$(5'h"b");

      LETC CSub: Bool <- #cheriotNonImm && #f7 == $$(7'h"14");
      LETC CMove: Bool <- #cheriot1Src && #rs2Idx == $$(5'h"a");
      
      LETC CTestSubset: Bool <- #cheriotNonImm && #f7 == $$(7'h"20");
      LETC CSetEqual: Bool <- #cheriotNonImm && #f7 == $$(7'h"21");

      LETC CSpecialRw: Bool <- #cheriotNonImm && #f7 == $$(7'h"1");

      LETC Crrl: Bool <- #cheriot1Src && #rs2Idx == $8;
      LETC Cram: Bool <- #cheriot1Src && #rs2Idx == $9;

      LETC MultiCycle: Bool <- #Load;

      LETC Src1Pc: Bool <- Kor [#CJal; #Branch; #AuiPcc];
      LETC InvSrc2: Bool <- Kor [#SltI; #SltuI; #Slt; #Sltu; #Sub; #CSub; #CGetLen];
      LETC Src2Zero: Bool <- Kor [#CSetAddr; #CGetAddr; #CSetHigh; #CAndPerm; #CClearTag;
                                  #CMove; #CSeal; #CUnseal; #CSetBounds; #CSetBoundsExact;
                                  #CSetBoundsRoundDown; #CSetBoundsImm];

      LETC ZeroExtendSrc1: Bool <- Kor [#SltuI; #SrlI; #Sltu; #Srl; #BranchUnsigned; #AuiPcc;
                                        #CIncAddr; #CIncAddrImm; #CSetAddr];
      LETC SltAll: Bool <- Kor [#SltI; #SltuI; #Slt; #Sltu];
      LETC AddAll: Bool <- Kor [#AddI; #Add; #Sub; #CIncAddr; #CIncAddrImm; #CSetAddr; #CSub];
      LETC XorAll: Bool <- Kor [#XorI; #Xor];
      LETC  OrAll: Bool <- Kor [#OrI; #Or; #CGetAddr; #CSetHigh; #CAndPerm; #CClearTag; #CMove; #CSeal;
                                #CUnseal; #CSetBounds; #CSetBoundsExact; #CSetBoundsRoundDown; #CSetBoundsImm];
      LETC AndAll: Bool <- Kor [#AndI; #And];
      LETC  SlAll: Bool <- Kor [#SllI; #Sll];
      LETC  SrAll: Bool <- Kor [#SrlI; #SraI; #Srl; #Sra];
      LETC SetBounds: Bool <- Kor [#CSetBounds; #CSetBoundsExact; #CSetBoundsImm; #CSetBoundsRoundDown];
      LETC SetBoundsExact: Bool <- #CSetBoundsExact;
      LETC BoundsSubset: Bool <- #CSetBoundsRoundDown;
      LETC BoundsFixedBase: Bool <- #CSetBoundsRoundDown;

      LETC CChangeAddr: Bool <- Kor [#CIncAddr; #CIncAddrImm; #CSetAddr; #AuiPcc];
      
      LETC isCsr: Bool <- #isSys && isNotZero (#f3$[1:0]);

      LETC SignExtendImmNoLoadNoCJalr <- Kor [#AddI; #SltI; #XorI; #OrI; #AndI; #CIncAddrImm];
      LETC SignExtendImm: Bool <- Kor [#SignExtendImmNoLoadNoCJalr; #Load; #CJalr];
      LETC ZeroExtendImm: Bool <- Kor [#SltuI; #CSetBoundsImm; #SllI; #SrlI; #SraI];
      LETC AuiAll: Bool <- Kor [#AuiPcc; #AuiCgp];

      LETC ECallAll: Bool <- Kor [#ECall; #Wfi];

      LETC NotIllegal: Bool <- Kor [#Lui; #AuiAll; #CJal; #CJalr; #Branch; #Load; #Store;
                                    #AddAll; #SltAll; #XorAll; #OrAll; #AndAll; #SlAll; #SrAll;
                                    #Fence; #FenceI; #ECallAll; #EBreak; #MRet; #isCsr;
                                    #CGetPerm; #CGetType; #CGetBase; #CGetLen;
                                    #CGetTag; #CGetHigh; #CGetTop;
                                    #CTestSubset; #CSetEqual;
                                    #CSpecialRw; #Crrl; #Cram];

      LETC ReadReg1: Bool <- Kor [#AuiCgp; #CJalr; #Branch; #Load; #Store; #immediate; #nonImmediate;
                                  #isCsr; #cheriot];

      LETC ReadReg2: Bool <- Kor [#Branch; #Store; #immediate;
                                  (#cheriotNonImm && !Kor [#f7 == $$(7'h"7f"); #f7 == $1])];

      LETC WriteReg: Bool <- Kor [#Lui; #AuiAll; #CJal; #CJalr; #Load; #immediate; #nonImmediate;
                                  #isCsr; #cheriot];

      LETC auiLuiOffsetInst: Bit Imm20Sz <- auiLuiOffset inst;

      LETC rs1Idx: Bit RegFixedIdSz <- rs1Fixed inst;
      LETC rs2Idx: Bit RegFixedIdSz <- rs2Fixed inst;
      LETC rdIdx: Bit RegFixedIdSz <- rdFixed inst;

      LETC decImm: Bit DecImmSz <- Kor [ITE0 #SignExtendImm (SignExtendTo DecImmSz #immVal);
                                        ITE0 (#ZeroExtendImm || #isCsr) (ZeroExtendTo DecImmSz #immVal);
                                        ITE0 #Store (SignExtendTo DecImmSz ({< funct7 inst, rdFixed inst >}));
                                        ITE0 #Branch (SignExtendTo DecImmSz (branchOffset inst));
                                        ITE0 #CJal (jalOffset inst);
                                        ITE0 #AuiAll (SignExtend 1 #auiLuiOffsetInst);
                                        ITE0 #Lui ({<#auiLuiOffsetInst, $$WO~0>})
                                     ];

      LETC ImmExtRight: Bool <- Kor [#AuiAll; #Lui];

      LETC ImmForData: Bool <- Kor [#SignExtendImmNoLoadNoCJalr; #ZeroExtendImm; #AuiAll];
      LETC ImmForAddr: Bool <- Kor [#Branch; #CJal; #CJalr; #Load; #Store];

      LETC res: DecodeOut <-
                  STRUCT { "rs1Idx" ::= #rs1Idx ;
                           "rs2Idx" ::= #rs2Idx ;
                            "rdIdx" ::= #rdIdx ;
                           "decImm" ::= #decImm ;
                            "memSz" ::= #memSz ;

                       "Compressed" ::= $$false;
                      "ImmExtRight" ::= #ImmExtRight ;
                       "ImmForData" ::= #ImmForData ;
                       "ImmForAddr" ::= #ImmForAddr ;                           

                         "ReadReg1" ::= #ReadReg1 ;
                         "ReadReg2" ::= #ReadReg2 ;
                         "WriteReg" ::= #WriteReg ;
            
                       "MultiCycle" ::= #MultiCycle ;
            
                           "Src1Pc" ::= #Src1Pc ;
                          "InvSrc2" ::= #InvSrc2 ;
                         "Src2Zero" ::= #Src2Zero ;
                   "ZeroExtendSrc1" ::= #ZeroExtendSrc1 ;
                           "Branch" ::= #Branch ;
                         "BranchLt" ::= #BranchLt ;
                        "BranchNeg" ::= #BranchNeg ;
                              "Slt" ::= #SltAll ;
                              "Add" ::= #AddAll ;
                              "Xor" ::= #XorAll ;
                               "Or" ::= #OrAll ;
                              "And" ::= #AndAll ;
                               "Sl" ::= #SlAll ;
                               "Sr" ::= #SrAll ;
                            "Store" ::= #Store ;
                             "Load" ::= #Load ;
                     "LoadUnsigned" ::= #LoadUnsigned ;
                        "SetBounds" ::= #SetBounds ;
                   "SetBoundsExact" ::= #SetBoundsExact ;
                     "BoundsSubset" ::= #BoundsSubset ;
                  "BoundsFixedBase" ::= #BoundsFixedBase ;
              
                      "CChangeAddr" ::= #CChangeAddr ;
                           "AuiPcc" ::= #AuiPcc ;
                         "CGetBase" ::= #CGetBase ;
                          "CGetTop" ::= #CGetTop ;
                          "CGetLen" ::= #CGetLen ;
                         "CGetPerm" ::= #CGetPerm ;
                         "CGetType" ::= #CGetType ;
                          "CGetTag" ::= #CGetTag ;
                         "CGetHigh" ::= #CGetHigh ;
                             "Cram" ::= #Cram ;
                             "Crrl" ::= #Crrl ;
                        "CSetEqual" ::= #CSetEqual ;
                      "CTestSubset" ::= #CTestSubset ;
                         "CAndPerm" ::= #CAndPerm ;
                        "CClearTag" ::= #CClearTag ;
                         "CSetHigh" ::= #CSetHigh ;
                            "CMove" ::= #CMove ;
                            "CSeal" ::= #CSeal ;
                          "CUnseal" ::= #CUnseal ;
                
                             "CJal" ::= #CJal ;
                            "CJalr" ::= #CJalr ;
                           "AuiAll" ::= #AuiAll ;
                              "Lui" ::= #Lui ;
              
                       "CSpecialRw" ::= #CSpecialRw ;
                             "MRet" ::= #MRet ;
                            "ECall" ::= #ECallAll ;
                           "EBreak" ::= #EBreak ;
                           "FenceI" ::= #FenceI ;
                            "Fence" ::= #Fence ;
                       "NotIllegal" ::= #NotIllegal ;
              
                            "CsrRw" ::= #CsrRw ;
                           "CsrSet" ::= #CsrSet ;
                         "CsrClear" ::= #CsrClear ;
                           "CsrImm" ::= #CsrImm };
           
      RetE #res).

  Definition decodeCompQ0: DecodeOut ## ty :=
    ( LETC rdIdx: Bit RegFixedIdSz <- ZeroExtendTo RegFixedIdSz (inst$[4:2]);
      LETC rs2Idx: Bit RegFixedIdSz <- ZeroExtendTo RegFixedIdSz (inst$[4:2]);
      LETC f3: Bit 3 <- inst$[15:13];
      LETC CIncAddrImm: Bool <- isZero #f3;
      LETC rs1Idx: Bit RegFixedIdSz <- ITE #CIncAddrImm
                                         $sp
                                         (ZeroExtendTo RegFixedIdSz (inst$[9:7]));
      LETC memSz: Bit 2 <- #f3$[1:0];
      LETC Store: Bool <- unpack Bool (#f3$[2:2]);
      LETC Load: Bool <- !(#Store || #CIncAddrImm);
      LETC NotIllegal: Bool <- isNotZero (inst$[15:0]) && (isZero #f3 || unpack Bool (#memSz$[1:1]));
      LETC immMem_6_3: Bit 4 <- ({< (inst$[5:5]), (inst$[12:10]) >});
      LETC memDecImm <- ITE (unpack Bool (#memSz$[0:0]))
                          ({<(inst$[6:6]), #immMem_6_3, $$(wzero 3)>})
                          ({< $$(WO~0), #immMem_6_3, (inst$[6:6]), $$(wzero 2)>});
      LETC cIncImm <-  ({<(inst$[10:7]), (inst$[12:11]), (inst$[5:5]), (inst$[6:6]) , $$(wzero 2)>});
      LETC decImm: Bit DecImmSz <- ITE #CIncAddrImm
                                     (SignExtendTo DecImmSz #cIncImm)
                                     (SignExtendTo DecImmSz #memDecImm);
      LETC res: DecodeOut <-
                  STRUCT { "rs1Idx" ::= #rs1Idx ;
                           "rs2Idx" ::= #rs2Idx ;
                            "rdIdx" ::= #rdIdx ;
                           "decImm" ::= #decImm ;
                            "memSz" ::= #memSz ;

                       "Compressed" ::= $$true ;
                      "ImmExtRight" ::= $$false ;
                       "ImmForData" ::= #CIncAddrImm ;
                       "ImmForAddr" ::= !#CIncAddrImm ;

                         "ReadReg1" ::= $$true ;
                         "ReadReg2" ::= #Store ;
                         "WriteReg" ::= !#Store ;
            
                       "MultiCycle" ::= #Load ;
            
                           "Src1Pc" ::= $$false ;
                          "InvSrc2" ::= $$false ;
                         "Src2Zero" ::= $$false ;
                   "ZeroExtendSrc1" ::= #CIncAddrImm ;
                           "Branch" ::= $$false ;
                         "BranchLt" ::= $$false ;
                        "BranchNeg" ::= $$false ;
                              "Slt" ::= $$false ;
                              "Add" ::= #CIncAddrImm ;
                              "Xor" ::= $$false ;
                               "Or" ::= $$false ;
                              "And" ::= $$false ;
                               "Sl" ::= $$false ;
                               "Sr" ::= $$false ;
                            "Store" ::= #Store ;
                             "Load" ::= #Load ;
                     "LoadUnsigned" ::= $$false ;
                        "SetBounds" ::= $$false ;
                   "SetBoundsExact" ::= $$false ;
                     "BoundsSubset" ::= $$false ;
                  "BoundsFixedBase" ::= $$false ;
              
                      "CChangeAddr" ::= #CIncAddrImm ;
                           "AuiPcc" ::= $$false ;
                         "CGetBase" ::= $$false ;
                          "CGetTop" ::= $$false ;
                          "CGetLen" ::= $$false ;
                         "CGetPerm" ::= $$false ;
                         "CGetType" ::= $$false ;
                          "CGetTag" ::= $$false ;
                         "CGetHigh" ::= $$false ;
                             "Cram" ::= $$false ;
                             "Crrl" ::= $$false ;
                        "CSetEqual" ::= $$false ;
                      "CTestSubset" ::= $$false ;
                         "CAndPerm" ::= $$false ;
                        "CClearTag" ::= $$false ;
                         "CSetHigh" ::= $$false ;
                            "CMove" ::= $$false ;
                            "CSeal" ::= $$false ;
                          "CUnseal" ::= $$false ;
                
                             "CJal" ::= $$false ;
                            "CJalr" ::= $$false ;
                           "AuiAll" ::= $$false ;
                              "Lui" ::= $$false ;
              
                       "CSpecialRw" ::= $$false ;
                             "MRet" ::= $$false ;
                            "ECall" ::= $$false ;
                           "EBreak" ::= $$false ;
                           "FenceI" ::= $$false ;
                            "Fence" ::= $$false ;
                       "NotIllegal" ::= #NotIllegal ;
              
                            "CsrRw" ::= $$false ;
                           "CsrSet" ::= $$false ;
                         "CsrClear" ::= $$false ;
                           "CsrImm" ::= $$false };
          RetE #res).

  Definition decodeCompQ1: DecodeOut ## ty :=
    ( LETC f3: Bit 3 <- inst$[15:13];
      LETC rs1Idx: Bit RegFixedIdSz <- ITE (unpack Bool (#f3$[2:2]))
                                         (ZeroExtendTo RegFixedIdSz (inst$[9:7]))
                                         (ITE (#f3$[1:0] == $2) $c0 (inst$[11:7]));
      LETC rdIdx: Bit RegFixedIdSz <- ITE (unpack Bool (#f3$[2:2]))
                                         (ITE (#f3$[1:0] == $1) $c0 (ZeroExtendTo RegFixedIdSz (inst$[9:7])))
                                         (inst$[11:7]);
      LETC rs2Idx: Bit RegFixedIdSz <- ITE (isNotZero (#f3$[1:0])) $0 (ZeroExtendTo RegFixedIdSz (inst$[4:2]));

      LETC AddI: Bool <- (isZero #f3 || (#f3 == $2));
      LETC CJal: Bool <- (#f3$[1:0]) == $1;

      LETC cjalImm: Bit DecImmSz <- SignExtendTo DecImmSz ({<(inst$[12:12]), (inst$[8:8]), (inst$[10:9]),
                                          (inst$[6:6]), (inst$[7:7]), (inst$[2:2]), (inst$[11:11]), (inst$[5:3]),
                                          $$WO~0>});
      
      LETC CIncAddrImm: Bool <- #f3 == $3 && (inst$[11:7] == $2);

      LETC cIncImm: Bit DecImmSz <- SignExtendTo DecImmSz ({< (inst$[12:12]), (inst$[4:3]), (inst$[5:5]),
                                          (inst$[2:2]), (inst$[6:6]), $$(wzero 4) >});

      LETC Lui: Bool <- #f3 == $3 && (inst$[11:7] != $2);

      LETC alu: Bool <- #f3 == $4;
      LETC someAlu: Bool <- inst$[12:12] == $0;

      LETC SrlI: Bool <- #alu && (isZero (inst$[11:10])) && #someAlu;
      LETC SraI: Bool <- #alu && (inst$[11:10] == $1) && #someAlu;
      LETC AndI: Bool <- #alu && (inst$[11:10] == $2);

      LETC arith: Bool <- #alu && (inst$[11:10] == $3) && #someAlu;

      LETC Sub: Bool <- #arith && isZero (inst$[6:5]);
      LETC Xor: Bool <- #arith && (inst$[6:5] == $1);
      LETC  Or: Bool <- #arith && (inst$[6:5] == $2);
      LETC And: Bool <- #arith && (inst$[6:5] == $3);

      LETC Branch: Bool <- isAllOnes (#f3$[2:1]);
      LETC BranchNeg: Bool <- unpack Bool (#f3$[0:0]);

      LETC branchImm: Bit DecImmSz <- SignExtendTo DecImmSz ({<(inst$[12:12]), (inst$[6:5]),
                                            (inst$[2:2]), (inst$[11:10]), (inst$[4:3]), $$WO~0 >});

      LETC normalImm: Bit 6 <- ({< inst$[12:12], (inst$[6:2]) >});

      LETC decImm: Bit DecImmSz <- caseDefault [(#CJal, #cjalImm);
                                                (#Branch, #branchImm);
                                                (#CIncAddrImm, #cIncImm);
                                                (#Lui, SignExtendTo DecImmSz ({<#normalImm, $$WO~0>}))]
                                     (SignExtendTo DecImmSz #normalImm);

      LETC ImmForData: Bool <- Kor [#AddI; #CIncAddrImm; #Lui; #SrlI; #SraI; #AndI];
      LETC ImmForAddr: Bool <- Kor [#CJal; #Branch];

      LETC ReadReg1: Bool <- !Kor [#CJal; #Lui];
      LETC ReadReg2: Bool <- (#f3 == $4) && (inst$[11:10] == $3);
      LETC WriteReg: Bool <- !#Branch;
      
      LETC NotIllegal: Bool <- #f3 == $4 && !(unpack Bool (inst$[12:12]));

      LETC res: DecodeOut <-
                  STRUCT { "rs1Idx" ::= #rs1Idx ;
                           "rs2Idx" ::= #rs2Idx ;
                            "rdIdx" ::= #rdIdx ;
                           "decImm" ::= #decImm ;
                            "memSz" ::= $0 ;

                       "Compressed" ::= $$true;
                      "ImmExtRight" ::= #Lui ;
                       "ImmForData" ::= #ImmForData ;
                       "ImmForAddr" ::= #ImmForAddr ;

                         "ReadReg1" ::= #ReadReg1 ;
                         "ReadReg2" ::= #ReadReg2 ;
                         "WriteReg" ::= #WriteReg ;
            
                       "MultiCycle" ::= $$false ;
            
                           "Src1Pc" ::= Kor [#CJal; #Branch] ;
                          "InvSrc2" ::= #Sub ;
                         "Src2Zero" ::= $$false ;
                   "ZeroExtendSrc1" ::= #CIncAddrImm ;
                           "Branch" ::= #Branch ;
                         "BranchLt" ::= $$false ;
                        "BranchNeg" ::= #BranchNeg ;
                              "Slt" ::= $$false ;
                              "Add" ::= Kor [#AddI; #CIncAddrImm; #Sub] ;
                              "Xor" ::= #Xor ;
                               "Or" ::= $$false ;
                              "And" ::= #And ;
                               "Sl" ::= $$false ;
                               "Sr" ::= (#SrlI || #SraI) ;
                            "Store" ::= $$false ;
                             "Load" ::= $$false ;
                     "LoadUnsigned" ::= $$false ;
                        "SetBounds" ::= $$false ;
                   "SetBoundsExact" ::= $$false ;
                     "BoundsSubset" ::= $$false ;
                  "BoundsFixedBase" ::= $$false ;
              
                      "CChangeAddr" ::= #CIncAddrImm ;
                           "AuiPcc" ::= $$false ;
                         "CGetBase" ::= $$false ;
                          "CGetTop" ::= $$false ;
                          "CGetLen" ::= $$false ;
                         "CGetPerm" ::= $$false ;
                         "CGetType" ::= $$false ;
                          "CGetTag" ::= $$false ;
                         "CGetHigh" ::= $$false ;
                             "Cram" ::= $$false ;
                             "Crrl" ::= $$false ;
                        "CSetEqual" ::= $$false ;
                      "CTestSubset" ::= $$false ;
                         "CAndPerm" ::= $$false ;
                        "CClearTag" ::= $$false ;
                         "CSetHigh" ::= $$false ;
                            "CMove" ::= $$false ;
                            "CSeal" ::= $$false ;
                          "CUnseal" ::= $$false ;
                
                             "CJal" ::= #CJal ;
                            "CJalr" ::= $$false ;
                           "AuiAll" ::= $$false ;
                              "Lui" ::= $$false ;
              
                       "CSpecialRw" ::= $$false ;
                             "MRet" ::= $$false ;
                            "ECall" ::= $$false ;
                           "EBreak" ::= $$false ;
                           "FenceI" ::= $$false ;
                            "Fence" ::= $$false ;
                       "NotIllegal" ::= #NotIllegal ;
              
                            "CsrRw" ::= $$false ;
                           "CsrSet" ::= $$false ;
                         "CsrClear" ::= $$false ;
                           "CsrImm" ::= $$false };
      RetE #res).

  Definition decodeCompQ2: DecodeOut ## ty :=
    ( LETC f3: Bit 3 <- inst$[15:13];

      LETC rs2Idx: Bit RegFixedIdSz <- inst$[6:2];
      LETC rs1Idx: Bit RegFixedIdSz <- ITE (unpack Bool (#f3$[1:1]))
                                         $sp
                                         (ITE (#f3 == $4 && !(unpack Bool (inst$[12:12])) && isNotZero #rs2Idx)
                                            $c0
                                            inst$[11:7]);
      LETC rdIdx: Bit RegFixedIdSz <- ITE (#f3 == $4 && isZero #rs2Idx && !(unpack Bool (inst$[12:12])))
                                        $c0
                                        (inst$[11:7]);
      
      LETC SllI: Bool <- isZero #f3;

      LETC Load: Bool <- #f3$[2:1] == $1;
      LETC Store: Bool <- #f3$[2:1] == $3;

      LETC memSz: Bit MemSzSz <- ({< $$WO~1, (#f3$[0:0])>});

      LETC Add: Bool <- #f3 == $4 && isNotZero #rs2Idx && isNotZero (inst$[11:7]);
      LETC CJalr: Bool <- #f3 == $4 && isZero #rs2Idx && isNotZero (inst$[11:7]);
      LETC EBreak: Bool <- #f3 == $4 && isZero #rs2Idx && isZero (inst$[11:7]) && unpack Bool (inst$[12:12]);

      LETC sllImm: Bit DecImmSz <- ZeroExtendTo DecImmSz #rs2Idx;
      LETC ldImm: Bit 9 <- ({< ITE0 (unpack Bool (#f3$[0:0])) (inst$[4:4]), (inst$[3:2]), (inst$[12:12]),
                               (inst$[6:5]), ITE0 (!(unpack Bool (#f3$[0:0]))) (inst$[4:4]), $$(wzero 2) >});

      LETC stImm: Bit 9 <- ({< ITE0 (unpack Bool (#f3$[0:0])) (inst$[9:9]), (inst$[8:7]), (inst$[12:10]),
                               ITE0 (!(unpack Bool (#f3$[0:0]))) (inst$[9:9]), $$(wzero 2) >});

      LETC decImm: Bit DecImmSz <- Kor [ITE0 #SllI #sllImm;
                                        ITE0 (#Load || #Store) (ZeroExtendTo DecImmSz (ITE #Load #ldImm #stImm))];

      LETC res: DecodeOut <-
                  STRUCT { "rs1Idx" ::= #rs1Idx ;
                           "rs2Idx" ::= #rs2Idx ;
                            "rdIdx" ::= #rdIdx ;
                           "decImm" ::= #decImm ;
                            "memSz" ::= #memSz ;

                       "Compressed" ::= $$true;
                      "ImmExtRight" ::= $$false ;
                       "ImmForData" ::= #SllI ;
                       "ImmForAddr" ::= Kor [#Load; #Store; #CJalr] ;

                         "ReadReg1" ::= !#EBreak ;
                         "ReadReg2" ::= (unpack Bool (#f3$[2:2]) && !#EBreak) ;
                         "WriteReg" ::= !(Kor [#EBreak; #Store]) ;
            
                       "MultiCycle" ::= $$false ;
            
                           "Src1Pc" ::= $$false ;
                          "InvSrc2" ::= $$false ;
                         "Src2Zero" ::= $$false ;
                   "ZeroExtendSrc1" ::= $$false ;
                           "Branch" ::= $$false ;
                         "BranchLt" ::= $$false ;
                        "BranchNeg" ::= $$false ;
                              "Slt" ::= $$false ;
                              "Add" ::= #Add ;
                              "Xor" ::= $$false ;
                               "Or" ::= $$false ;
                              "And" ::= $$false ;
                               "Sl" ::= #SllI ;
                               "Sr" ::= $$false ;
                            "Store" ::= #Store ;
                             "Load" ::= #Load ;
                     "LoadUnsigned" ::= $$false ;
                        "SetBounds" ::= $$false ;
                   "SetBoundsExact" ::= $$false ;
                     "BoundsSubset" ::= $$false ;
                  "BoundsFixedBase" ::= $$false ;
              
                      "CChangeAddr" ::= $$false ;
                           "AuiPcc" ::= $$false ;
                         "CGetBase" ::= $$false ;
                          "CGetTop" ::= $$false ;
                          "CGetLen" ::= $$false ;
                         "CGetPerm" ::= $$false ;
                         "CGetType" ::= $$false ;
                          "CGetTag" ::= $$false ;
                         "CGetHigh" ::= $$false ;
                             "Cram" ::= $$false ;
                             "Crrl" ::= $$false ;
                        "CSetEqual" ::= $$false ;
                      "CTestSubset" ::= $$false ;
                         "CAndPerm" ::= $$false ;
                        "CClearTag" ::= $$false ;
                         "CSetHigh" ::= $$false ;
                            "CMove" ::= $$false ;
                            "CSeal" ::= $$false ;
                          "CUnseal" ::= $$false ;
                
                             "CJal" ::= $$false ;
                            "CJalr" ::= #CJalr ;
                           "AuiAll" ::= $$false ;
                              "Lui" ::= $$false ;
              
                       "CSpecialRw" ::= $$false ;
                             "MRet" ::= $$false ;
                            "ECall" ::= $$false ;
                           "EBreak" ::= #EBreak ;
                           "FenceI" ::= $$false ;
                            "Fence" ::= $$false ;
                       "NotIllegal" ::= $$false ;
              
                            "CsrRw" ::= $$false ;
                           "CsrSet" ::= $$false ;
                         "CsrClear" ::= $$false ;
                           "CsrImm" ::= $$false };
      RetE #res).

  Definition decode : DecodeOut ## ty :=
    ( LETE compQ0: DecodeOut <- decodeCompQ0;
      LETE compQ1: DecodeOut <- decodeCompQ1;
      LETE compQ2: DecodeOut <- decodeCompQ2;
      LETE fullInst: DecodeOut <- decodeFullInst;
      LETC instSz: Bit 2 <- TruncLsbTo 2 _ inst;
      LETC res: DecodeOut <- ITE (unpack Bool (#instSz$[1:1]))
                               (ITE (unpack Bool (#instSz$[0:0]))
                                  #fullInst
                                  #compQ2)
                               (ITE (unpack Bool (#instSz$[0:0]))
                                  #compQ1
                                  #compQ0);
      RetE #res).
End Decode.

(* MemBanks, Clut, Pipelines (Load, LoadCap, Store, Fetch) *)
Section Alu.
  Variable ty: Kind -> Type.

  (* Note: A single PCCap and tag exception when we have a superscalar processor;
     other values are repeated per lane *)
  Variable pcTag: Bool @# ty.
  Variable pcCap: ECap @# ty.

  Variable aluIn : AluIn @# ty.
  Local Open Scope kami_expr.
  
  Local Definition            pcVal: Addr @# ty := aluIn @% "pcAluOut" @% "pcVal".
  Local Definition  BoundsException: Bool @# ty := aluIn @% "pcAluOut" @% "BoundsException".
  
  Local Definition  regs: Array NumRegs _ @# ty := aluIn @% "regs".
  Local Definition waits: Array NumRegs _ @# ty := aluIn @% "waits".

  Local Definition             csrs: Csrs @# ty := aluIn @% "csrs".
  Local Definition      mcycle: Bit DXlen @# ty := csrs @% "mcycle".
  Local Definition       mtime: Bit DXlen @# ty := csrs @% "mtime".
  Local Definition    minstret: Bit DXlen @# ty := csrs @% "minstret".
  Local Definition           mshwm: Bit _ @# ty := csrs @% "mshwm".
  Local Definition          mshwmb: Bit _ @# ty := csrs @% "mshwmb".

  Local Definition               ie: Bool @# ty := csrs @% "ie".
  Local Definition        interrupt: Bool @# ty := csrs @% "interrupt".
  Local Definition   mcause: Bit McauseSz @# ty := csrs @% "mcause".
  Local Definition            mtval: Addr @# ty := csrs @% "mtval".

  Local Definition             scrs: Scrs @# ty := aluIn @% "scrs".
  Local Definition  mtcc: FullECapWithTag @# ty := scrs @% "mtcc".
  Local Definition  mtdc: FullECapWithTag @# ty := scrs @% "mtdc".
  Local Definition            mscratch: _ @# ty := scrs @% "mscratchc" : FullECapWithTag @# _.
  Local Definition               mepcc: _ @# ty := scrs @% "mepcc" : FullECapWithTag @# _.

  Local Definition interrupts: Interrupts @# ty := aluIn @% "interrupts".
  Local Definition              mei: Bool @# ty := interrupts @% "mei".
  Local Definition              mti: Bool @# ty := interrupts @% "mti".
  Local Definition   incoming: Interrupts @# ty := aluIn @% "incoming".
  Local Definition              mep: Bool @# ty := incoming @% "mei".
  Local Definition              mtp: Bool @# ty := incoming @% "mti".

  Local Definition         rs1IdxFixed: _ @# ty := aluIn @% "decodeOut" @% "rs1Idx" : Bit RegFixedIdSz @# ty.
  Local Definition         rs2IdxFixed: _ @# ty := aluIn @% "decodeOut" @% "rs2Idx" : Bit RegFixedIdSz @# ty.
  Local Definition          rdIdxFixed: _ @# ty := aluIn @% "decodeOut" @% "rdIdx" : Bit RegFixedIdSz @# ty.
  Local Definition   decImm: Bit DecImmSz @# ty := aluIn @% "decodeOut" @% "decImm".
  Local Definition     memSz: Bit MemSzSz @# ty := aluIn @% "decodeOut" @% "memSz".

  Local Definition       Compressed: Bool @# ty := aluIn @% "decodeOut" @% "Compressed".
  Local Definition      ImmExtRight: Bool @# ty := aluIn @% "decodeOut" @% "ImmExtRight".
  Local Definition       ImmForData: Bool @# ty := aluIn @% "decodeOut" @% "ImmForData".
  Local Definition       ImmForAddr: Bool @# ty := aluIn @% "decodeOut" @% "ImmForAddr".

  Local Definition         ReadReg1: Bool @# ty := aluIn @% "decodeOut" @% "ReadReg1".
  Local Definition         ReadReg2: Bool @# ty := aluIn @% "decodeOut" @% "ReadReg2".
  Local Definition         WriteReg: Bool @# ty := aluIn @% "decodeOut" @% "WriteReg".

  Local Definition       MultiCycle: Bool @# ty := aluIn @% "decodeOut" @% "MultiCycle".
  
  Local Definition           Src1Pc: Bool @# ty := aluIn @% "decodeOut" @% "Src1Pc".
  Local Definition          InvSrc2: Bool @# ty := aluIn @% "decodeOut" @% "InvSrc2".
  Local Definition         Src2Zero: Bool @# ty := aluIn @% "decodeOut" @% "Src2Zero".
  Local Definition   ZeroExtendSrc1: Bool @# ty := aluIn @% "decodeOut" @% "ZeroExtendSrc1".
  Local Definition           Branch: Bool @# ty := aluIn @% "decodeOut" @% "Branch".
  Local Definition         BranchLt: Bool @# ty := aluIn @% "decodeOut" @% "BranchLt".
  Local Definition        BranchNeg: Bool @# ty := aluIn @% "decodeOut" @% "BranchNeg".
  Local Definition              Slt: Bool @# ty := aluIn @% "decodeOut" @% "Slt".
  Local Definition              Add: Bool @# ty := aluIn @% "decodeOut" @% "Add".
  Local Definition              Xor: Bool @# ty := aluIn @% "decodeOut" @% "Xor".
  Local Definition               Or: Bool @# ty := aluIn @% "decodeOut" @% "Or".
  Local Definition              And: Bool @# ty := aluIn @% "decodeOut" @% "And".
  Local Definition               Sl: Bool @# ty := aluIn @% "decodeOut" @% "Sl".
  Local Definition               Sr: Bool @# ty := aluIn @% "decodeOut" @% "Sr".
  Local Definition            Store: Bool @# ty := aluIn @% "decodeOut" @% "Store".
  Local Definition             Load: Bool @# ty := aluIn @% "decodeOut" @% "Load".
  Local Definition     LoadUnsigned: Bool @# ty := aluIn @% "decodeOut" @% "LoadUnsigned".
  Local Definition        SetBounds: Bool @# ty := aluIn @% "decodeOut" @% "SetBounds".
  Local Definition   SetBoundsExact: Bool @# ty := aluIn @% "decodeOut" @% "SetBoundsExact".
  Local Definition     BoundsSubset: Bool @# ty := aluIn @% "decodeOut" @% "BoundsSubset".
  Local Definition  BoundsFixedBase: Bool @# ty := aluIn @% "decodeOut" @% "BoundsFixedBase".

  Local Definition      CChangeAddr: Bool @# ty := aluIn @% "decodeOut" @% "CChangeAddr".
  Local Definition           AuiPcc: Bool @# ty := aluIn @% "decodeOut" @% "AuiPcc".
  Local Definition         CGetBase: Bool @# ty := aluIn @% "decodeOut" @% "CGetBase".
  Local Definition          CGetTop: Bool @# ty := aluIn @% "decodeOut" @% "CGetTop".
  Local Definition          CGetLen: Bool @# ty := aluIn @% "decodeOut" @% "CGetLen".
  Local Definition         CGetPerm: Bool @# ty := aluIn @% "decodeOut" @% "CGetPerm".
  Local Definition         CGetType: Bool @# ty := aluIn @% "decodeOut" @% "CGetType".
  Local Definition          CGetTag: Bool @# ty := aluIn @% "decodeOut" @% "CGetTag".
  Local Definition         CGetHigh: Bool @# ty := aluIn @% "decodeOut" @% "CGetHigh".
  Local Definition             Cram: Bool @# ty := aluIn @% "decodeOut" @% "Cram".
  Local Definition             Crrl: Bool @# ty := aluIn @% "decodeOut" @% "Crrl".
  Local Definition        CSetEqual: Bool @# ty := aluIn @% "decodeOut" @% "CSetEqual".
  Local Definition      CTestSubset: Bool @# ty := aluIn @% "decodeOut" @% "CTestSubset".
  Local Definition         CAndPerm: Bool @# ty := aluIn @% "decodeOut" @% "CAndPerm".
  Local Definition        CClearTag: Bool @# ty := aluIn @% "decodeOut" @% "CClearTag".
  Local Definition         CSetHigh: Bool @# ty := aluIn @% "decodeOut" @% "CSetHigh".
  Local Definition            CMove: Bool @# ty := aluIn @% "decodeOut" @% "CMove".
  Local Definition            CSeal: Bool @# ty := aluIn @% "decodeOut" @% "CSeal".
  Local Definition          CUnseal: Bool @# ty := aluIn @% "decodeOut" @% "CUnseal".
  
  Local Definition             CJal: Bool @# ty := aluIn @% "decodeOut" @% "CJal".
  Local Definition            CJalr: Bool @# ty := aluIn @% "decodeOut" @% "CJalr".
  Local Definition           AuiAll: Bool @# ty := aluIn @% "decodeOut" @% "AuiAll".
  Local Definition              Lui: Bool @# ty := aluIn @% "decodeOut" @% "Lui".

  Local Definition       CSpecialRw: Bool @# ty := aluIn @% "decodeOut" @% "CSpecialRw".
  Local Definition             MRet: Bool @# ty := aluIn @% "decodeOut" @% "MRet".
  Local Definition            ECall: Bool @# ty := aluIn @% "decodeOut" @% "ECall".
  Local Definition           EBreak: Bool @# ty := aluIn @% "decodeOut" @% "EBreak".
  Local Definition           FenceI: Bool @# ty := aluIn @% "decodeOut" @% "FenceI".
  Local Definition            Fence: Bool @# ty := aluIn @% "decodeOut" @% "Fence".
  Local Definition       NotIllegal: Bool @# ty := aluIn @% "decodeOut" @% "NotIllegal".

  Local Definition            CsrRw: Bool @# ty := aluIn @% "decodeOut" @% "CsrRw".
  Local Definition           CsrSet: Bool @# ty := aluIn @% "decodeOut" @% "CsrSet".
  Local Definition         CsrClear: Bool @# ty := aluIn @% "decodeOut" @% "CsrClear".
  Local Definition           CsrImm: Bool @# ty := aluIn @% "decodeOut" @% "CsrImm".

  Local Notation ITE0 x y := (ITE x y (Const ty Default)).
  Local Notation GetCsrIdx x := $$(NToWord CsrIdSz x).

  Local Definition saturatedMax {n} (e: Bit (n + 1) @# ty) :=
    ITE (unpack Bool (TruncMsbTo 1 n e)) $$(wones n) (TruncLsbTo n 1 e).

  Local Definition exception x := (STRUCT { "valid" ::= $$true;
                                            "data" ::= x } : Maybe (Bit CapExceptSz) @# ty ).

  Local Definition regIdxWrong (idx: Bit RegFixedIdSz @# ty) :=
    isNotZero (TruncMsbTo (RegFixedIdSz - RegIdSz) RegIdSz idx).

  Definition alu : AluOut ## ty :=
    ( LETC rdIdx: Bit RegIdSz <- TruncLsbTo RegIdSz _ rdIdxFixed;
      LETC rs1Idx: Bit RegIdSz <- TruncLsbTo RegIdSz _ rs1IdxFixed;
      LETC rs2Idx: Bit RegIdSz <- TruncLsbTo RegIdSz _ rs2IdxFixed;
      LETC immVal: Bit Imm12Sz <- TruncLsbTo Imm12Sz _ decImm;
      LETC fullImmXlen <- ITE ImmExtRight ({< decImm, $$(wzero 11) >}) (SignExtendTo Xlen decImm);
      LETC fullImmSXlen <- SignExtend 1 #fullImmXlen;

      LETC reg1 : FullECapWithTag <- ITE (isNotZero #rs1Idx) (regs @[ #rs1Idx ]) (Const ty Default);
      LETC tag1 : Bool <- #reg1 @% "tag";
      LETC cap1 : ECap <- #reg1 @% "ecap";
      LETC val1 : Addr <- #reg1 @% "addr";
      LETC reg2 : FullECapWithTag <- ITE (isNotZero #rs1Idx) (regs @[ #rs2Idx ]) (Const ty Default);
      LETC tag2 : Bool <- #reg2 @% "tag";
      LETC cap2 : ECap <- #reg2 @% "ecap";
      LETC val2 : Addr <- #reg2 @% "addr";

      LETC wait1 : Bool <- waits @[ #rs1Idx ];
      LETC wait2 : Bool <- waits @[ #rs2Idx ];

      LETC cap1Base <- #cap1 @% "base";
      LETC cap1Top <- #cap1 @% "top";
      LETC cap1Perms <- #cap1 @% "perms";
      LETC cap1OType <- #cap1 @% "oType";
      LETC cap2Base <- #cap2 @% "base";
      LETC cap2Top <- #cap2 @% "top";
      LETC cap2Perms <- #cap2 @% "perms";
      LETC cap2OType <- #cap2 @% "oType";
      LETC cap1NotSealed <- isNotSealed #cap1OType;
      LETC cap2NotSealed <- isNotSealed #cap2OType;

      LETC src1 <- ITE Src1Pc pcVal #val1;
      LETC src2Full <- ITE ImmForData
                         #fullImmSXlen
                         (SignExtend 1 (ITE0 (!Src2Zero) #val2));
      LETC adderSrc1 <- ITE CGetLen #cap1Top
                          (ITE ZeroExtendSrc1 (ZeroExtend 1 #src1) (SignExtend 1 #src1));
      LETC adderSrc2 <- ITE CGetLen #cap1Base #src2Full;
      LETC adderSrc2Fixed <- ITE InvSrc2 (~#adderSrc2) #adderSrc2;
      LETC carryExt  <- ZeroExtend Xlen (pack InvSrc2);
      LETC adderResFull <- #adderSrc1 + #adderSrc2Fixed + #carryExt;
      LETC adderResZero <- isZero #adderResFull;
      LETC adderCarryBool <- unpack Bool (TruncMsbTo 1 Xlen #adderResFull);
      LETC branchTakenPos <- ITE BranchLt #adderCarryBool #adderResZero;
      LETC branchTaken <- BranchNeg ^^ #branchTakenPos;
      LETC adderRes: Data <- TruncLsbTo Xlen 1 #adderResFull;
      LETC src2 <- TruncLsbTo Xlen 1 #src2Full;
      LETC xorRes <- #val1 .^ #src2;
      LETC orRes <- #val1 .| #src2;
      LETC andRes <- #val1 .& #src2;
      LETC shiftAmt <- TruncLsbTo (Nat.log2_up Xlen) _ #src2;
      LETC slRes <- #val1 << #shiftAmt;
      LETC srRes <- TruncLsbTo Xlen 1 (#adderSrc1 >>> #shiftAmt);

      LETC resAddrValFullTemp <- (ZeroExtend 1 #src1) + ITE0 ImmForAddr #fullImmSXlen;
      LETC resAddrValFull <- {< TruncMsbTo Xlen 1 #resAddrValFullTemp,
          ITE CJalr $$WO~0 (TruncLsbTo 1 Xlen #resAddrValFullTemp) >};
      LETC resAddrVal <- TruncLsbTo Xlen 1 #resAddrValFull;
      LETC resAddrCarryBool <- unpack Bool (TruncMsbTo 1 Xlen #resAddrValFull);

      LETC seal_unseal <- CSeal || CUnseal;

      LETC load_store <- Load || Store;
      LETC cjal_cjalr <- CJal || CJalr;
      LETC branch_jump <- Branch || #cjal_cjalr;
      LETC branch_jump_load_store <- #branch_jump || #load_store;

      LETC change_addr <- #branch_jump_load_store || CChangeAddr;

      LETC baseCheckBase <- caseDefault [(Src1Pc, pcCap @% "base"); (#seal_unseal, #cap2Base)] #cap1Base;
      LETC baseCheckAddr <- caseDefault [(CSeal, ZeroExtend 1 #val2); (CUnseal, ZeroExtendTo (Xlen + 1) #cap1OType);
                                         (#branch_jump_load_store, #resAddrValFull);
                                         (CTestSubset, #cap2Base)]
                              #adderResFull;
      LETC baseCheck <- (#baseCheckBase <= #baseCheckAddr) &&
                          (!#change_addr || !(unpack Bool (TruncMsbTo 1 Xlen #baseCheckAddr)));

      LETC representableLimit <- getRepresentableLimit
                                   (ITE Src1Pc (pcCap @% "base") #cap1Base)
                                   (get_ECorrected_from_E (ITE Src1Pc (pcCap @% "E") (#cap1 @% "E")));
      LETC topCheckTop <- caseDefault [(#seal_unseal, #cap2Top);
                                       (#branch_jump || CChangeAddr, #representableLimit)]
                            #cap1Top;
      LETC topCheckAddr <-  caseDefault [(CSeal, ZeroExtend 1 #val2);
                                         (CUnseal, ZeroExtendTo (Xlen + 1) #cap1OType);
                                         (#branch_jump_load_store, #resAddrValFull);
                                         (CTestSubset, #cap2Top)]
                              #adderResFull;
      LETC addrPlus <- ITE #load_store ($1 << memSz) (ZeroExtend Xlen (pack (!CTestSubset)));
      LETC topCheckAddrFinal <- #topCheckAddr + #addrPlus;
      LETC topCheck <-
        (#topCheckAddrFinal <= #topCheckTop) &&
          (Kor [!(Kor [#change_addr; CSeal; CUnseal]);
                !(unpack Bool (TruncMsbTo 1 Xlen #topCheckAddrFinal));
                isZero (TruncLsbTo Xlen 1 #topCheckAddrFinal)]);

      LETC boundsRes <- #baseCheck && #topCheck;
      
      LETC cTestSubset <- #tag1 == #tag2 && #boundsRes && ((pack #cap1Perms .& pack #cap2Perms) == pack #cap2Perms);

      LETE encodedCap <- encodeCap #cap1;
      LETC cram_crrl <- Cram || Crrl;
      LETC boundsBase <- ZeroExtend 1 (ITE #cram_crrl $0 #val1);
      LETC boundsLength <- ZeroExtend 1 (ITE #cram_crrl #val1 #val2);
      LETE newBounds <- calculateBounds #boundsBase #boundsLength BoundsSubset BoundsFixedBase;
      LETC newBoundsTop <- #newBounds @% "base" + #newBounds @% "length";
      LETC cSetEqual <- #tag1 == #tag2 && #cap1 == #cap2 && #val1 == #val2;
      LETC zeroExtendBoolRes <- ZeroExtendTo Xlen (pack (Kor [ITE0 Slt #adderCarryBool;
                                                              ITE0 CGetTag #tag1;
                                                              ITE0 CSetEqual #cSetEqual;
                                                              ITE0 CTestSubset #cTestSubset]));

      LETC cAndPermMask <- TruncLsbTo (size CapPerms) (Xlen - size CapPerms) #val2;
      LETC cAndPermCapPerms <- unpack CapPerms (pack #cap1Perms .& #cAndPermMask);
      LETC cAndPermCap <- #cap1 @%[ "perms" <- #cAndPermCapPerms];
      LETC cAndPermTagNew <- (#cap1NotSealed ||
                                isAllOnes (pack ((unpack CapPerms (#cAndPermMask)) @%[ "GL" <- $$true ])));

      LETE cSetHighCap <- decodeCap (unpack Cap #val2) #val1;

      LETC cChangeAddrTagNew <- (Src1Pc || #cap1NotSealed) && #boundsRes;

      LETC cSealCap <- #cap1 @%[ "oType" <- TruncLsbTo CapOTypeSz (AddrSz - CapOTypeSz) #val2];
      LETC cSealTagNew <- #tag2 && #cap1NotSealed && #cap2NotSealed && (#cap2Perms @% "SE") && #boundsRes &&
                            isSealableAddr (#cap1Perms @% "EX") #val1;

      LETC cUnsealCap <- #cap1 @%[ "oType" <- @unsealed ty ]
                           @%[ "perms" <- #cap1Perms @%[ "GL" <- #cap1Perms @% "GL" && #cap2Perms @% "GL" ] ];
      LETC cUnsealTagNew <- #tag2 && !#cap1NotSealed && #cap2NotSealed && (#cap2Perms @% "US") && #boundsRes;

      LETC cSetBoundsCap <- #cap1 @%[ "E" <- #newBounds @% "E" ]
                              @%[ "top" <- #newBoundsTop ]
                              @%[ "base" <- #newBounds @% "base" ];

      LETC cJalJalrCap <- pcCap @%[ "oType" <- ITE0 (#rdIdx == $ra) (createBackwardSentry ie) ];
      LETC cJalrAddrCap <- #cap1 @%[ "oType" <- unsealed ty];
      LETC newIe <- ((CJalr && isInterruptEnabling #cap1OType) ||
                       (ie && !(CJalr && isInterruptDisabling #cap1OType)));
      LETC notSealedOrInheriting <- #cap1NotSealed || isInterruptInheriting #cap1OType;
      LETC cJalrSealedCond <-
        (ITE (#rdIdx == $c0)
           (ITE (#rs1Idx == $ra) (isBackwardSentry #cap1OType) #notSealedOrInheriting)
           (ITE (#rdIdx == $ra) (#cap1NotSealed || isForwardSentry #cap1OType) #notSealedOrInheriting));

      LETC isCsr <- Kor [CsrRw; CsrSet; CsrClear];

      LETC validCsr <- Kor [ #immVal == GetCsrIdx Mcycle;
                             #immVal == GetCsrIdx Mtime;
                             #immVal == GetCsrIdx Minstret;
                             #immVal == GetCsrIdx Mcycleh;
                             #immVal == GetCsrIdx Mtimeh;
                             #immVal == GetCsrIdx Minstreth;
                             #immVal == GetCsrIdx Mshwm;
                             #immVal == GetCsrIdx Mshwmb;
                             #immVal == GetCsrIdx Mstatus;
                             #immVal == GetCsrIdx Mcause;
                             #immVal == GetCsrIdx Mtval ];

      LETC capSrException <- Kor [CSpecialRw; MRet; #isCsr && #validCsr]
                             && !(pcCap @% "perms" @% "SR");
      LETC isCapMem <- memSz == $LgNumBytesFullCapSz;
      LETC capNotAligned <- isNotZero (TruncLsbTo LgNumBytesFullCapSz (AddrSz - LgNumBytesFullCapSz) #resAddrVal) &&
                              #isCapMem;
      LETC clcException <- Load && #capNotAligned;
      LETC cscException <- Store && #capNotAligned;

      LETC validScr <- Kor [ rs2IdxFixed == $Mtcc;
                             rs2IdxFixed == $Mtdc;
                             rs2IdxFixed == $Mscratchc;
                             rs2IdxFixed == $Mepcc ];

      LETC wrongRegId <- Kor [ ReadReg1 && regIdxWrong rs1IdxFixed;
                               ReadReg2 && regIdxWrong rs2IdxFixed;
                               WriteReg && regIdxWrong rdIdxFixed ];

      LETC illegal <- Kor [!NotIllegal; #isCsr && !#validCsr; CSpecialRw && !#validScr; #wrongRegId];

      LETC capException <-
        (* Note: Kor is correct because of disjointness of capSrException with rest *)
        Kor [ ITE0 #capSrException (exception $SrViolation) ;
              ITE (#load_store && !#tag1) (exception $TagViolation)
                (ITE (#load_store && !#cap1NotSealed ||
                        (CJalr && (!#cJalrSealedCond || !#cap1NotSealed && isNotZero #immVal)))
                   (exception $SealViolation)
                   (ITE (Kor [(CJalr && !(#cap1Perms @% "EX")); (Load && !(#cap1Perms @% "LD"));
                              (Store && !(#cap1Perms @% "SD"))])
                      (exception (Kor [ ITE0 (CJalr && !(#cap1Perms @% "EX")) $ExViolation;
                                        ITE0 (Load && !(#cap1Perms @% "LD")) $LdViolation;
                                        ITE0 (Store && !(#cap1Perms @% "SD")) $SdViolation ]))
                      (ITE (Store && #isCapMem && !(#cap1Perms @% "MC"))
                         (exception $McSdViolation)
                         (ITE0 (#load_store && !#boundsRes)
                            (exception $BoundsViolation) )))) ];

      LETC capExceptionVal <- #capException @% "data";
      LETC isCapException <- #capException @% "valid";
      LETC capExceptionSrc <- ITE0 (!#capSrException) rs1IdxFixed;

      LETC isException <- Kor [!pcTag; BoundsException;
                               #illegal; EBreak; ECall; #clcException; #cscException; #isCapException];

      LETC mcauseExceptionVal: Bit McauseSz <- ITE (!pcTag || BoundsException)
                                                 $CapException
                                                 (caseDefault [ (#illegal, $IllegalException);
                                                                (EBreak, $EBreakException);
                                                                (ECall, $ECallException) ]
                                                    (caseDefault [ (#clcException, $LdAlignException);
                                                                   (#cscException, $SdAlignException) ]
                                                       (ITE0 #isCapException $CapException)));

      LETC mtvalExceptionVal: Bit Xlen <-
                                ITE (!pcTag || BoundsException)
                                  (@ZeroExtendTo _ Xlen CapExceptSz (Kor [ITE0 (!pcTag) $TagViolation;
                                                                          ITE0 BoundsException $BoundsViolation]))
                                  (ITE (Kor [#illegal; EBreak; ECall])
                                     (Const ty Default)
                                     (ITE (#clcException || #cscException) #resAddrVal
                                        (ITE0 #isCapException
                                           (ZeroExtendTo Xlen ({< #capExceptionSrc, #capExceptionVal >})))));

      LETC saturated <- saturatedMax
                          (Kor [ITE0 CGetBase #cap1Base; ITE0 CGetTop #cap1Top; ITE0 CGetLen #adderResFull;
                                ITE0 Crrl (#newBounds @% "length") ]);

      LETC linkAddr <- pcVal + if HasComp then $(InstSz/8) else ITE Compressed $(InstSz/8) $(CompInstSz/8);

      LETC resVal <- Kor [ ITE0 Add #adderRes; ITE0 Lui #fullImmXlen;
                           ITE0 Xor #xorRes; ITE0 Or #orRes; ITE0 And #andRes;
                           ITE0 Sl #slRes; ITE0 Sr #srRes;
                           ITE0 CGetPerm (ZeroExtendTo Xlen (pack #cap1Perms));
                           ITE0 CGetType (ZeroExtendTo Xlen #cap1OType);
                           ITE0 CGetHigh (pack #encodedCap);
                           ITE0 #cjal_cjalr #linkAddr;
                           ITE0 Cram (TruncLsbTo Xlen 1 (#newBounds @% "cram"));
                           #saturated;
                           #zeroExtendBoolRes];

      LETC resTag <- (#tag1 && Kor [ CAndPerm && #cAndPermTagNew;
                                     CMove;
                                     CChangeAddr && #cChangeAddrTagNew;
                                     CSeal && #cSealTagNew;
                                     ITE0 SetBounds (!SetBoundsExact || (#newBounds @% "exact"));
                                     CUnseal && #cUnsealTagNew;
                                     #cjal_cjalr ]);

      LETC resCap <- Kor [ ITE0 CAndPerm #cAndPermCap;
                           ITE0 (Kor [CClearTag; CMove; CChangeAddr]) (ITE Src1Pc pcCap #cap1);
                           ITE0 CSetHigh #cSetHighCap;
                           ITE0 SetBounds #cSetBoundsCap;
                           ITE0 #cjal_cjalr #cJalJalrCap;
                           ITE0 CSeal #cSealCap;
                           ITE0 CUnseal #cUnsealCap ];

      LETC csrIn <- ITE CsrImm (ZeroExtendTo Xlen rs1IdxFixed) #val1;

      LETC mcycleLsb : Bit Xlen <- TruncLsbTo Xlen Xlen mcycle;
      LETC mcycleMsb : Bit Xlen <- TruncMsbTo Xlen Xlen mcycle;
      LETC mtimeLsb : Bit Xlen <- TruncLsbTo Xlen Xlen mtime;
      LETC mtimeMsb : Bit Xlen <- TruncMsbTo Xlen Xlen mtime;
      LETC minstretLsb : Bit Xlen <- TruncLsbTo Xlen Xlen minstret;
      LETC minstretMsb : Bit Xlen <- TruncMsbTo Xlen Xlen minstret;
      LETC minstretInc : Bit DXlen <- minstret + $1;
      LETC minstretIncLsb : Bit Xlen <- TruncLsbTo Xlen Xlen #minstretInc;
      LETC minstretIncMsb : Bit Xlen <- TruncMsbTo Xlen Xlen #minstretInc;

      LETC csrCurr <- Kor [ ITE0 (#immVal == GetCsrIdx Mcycle) #mcycleLsb;
                            ITE0 (#immVal == GetCsrIdx Mtime) #mtimeLsb;
                            ITE0 (#immVal == GetCsrIdx Minstret) #minstretLsb;
                            ITE0 (#immVal == GetCsrIdx Mcycleh) #mcycleMsb;
                            ITE0 (#immVal == GetCsrIdx Mtimeh) #mtimeMsb;
                            ITE0 (#immVal == GetCsrIdx Minstreth) #minstretMsb;
                            ITE0 (#immVal == GetCsrIdx Mshwm) ({< mshwm, $$(wzero MshwmAlign) >});
                            ITE0 (#immVal == GetCsrIdx Mshwmb) ({< mshwmb, $$(wzero MshwmAlign) >});
                            ITE0 (#immVal == GetCsrIdx Mstatus)
                              (ZeroExtendTo Xlen ({< pack ie, $$(wzero (IeBit-1)) >}));
                            ITE0 (#immVal == GetCsrIdx Mcause) ({< pack interrupt, ZeroExtendTo (Xlen - 1) mcause >});
                            ITE0 (#immVal == GetCsrIdx Mtval) mtval ];

      LETC csrOut <- Kor [ ITE0 CsrRw #csrIn;
                           ITE0 CsrSet (#csrCurr .| #csrIn);
                           ITE0 CsrClear (#csrCurr .& ~#csrIn) ];

      LETC newMcycle: Bit DXlen <- ({< ITE (!#isException && #isCsr && #immVal == GetCsrIdx Mcycleh)
                                         #csrOut
                                         #mcycleMsb,
                                       ITE (!#isException && #isCsr && #immVal == GetCsrIdx Mcycle)
                                         #csrOut
                                         #mcycleLsb >});

      LETC newMtime: Bit DXlen <- ({< ITE (!#isException && #isCsr && #immVal == GetCsrIdx Mtimeh)
                                        #csrOut
                                        #mtimeMsb,
                                      ITE (!#isException && #isCsr && #immVal == GetCsrIdx Mtime)
                                        #csrOut
                                        #mtimeLsb >});

      LETC newMinstret: Bit DXlen <-
                          ITE #isException
                            minstret
                            ({< ITE (#isCsr && #immVal == GetCsrIdx Minstreth) #csrOut #minstretIncMsb,
                                ITE (#isCsr && #immVal == GetCsrIdx Minstret)  #csrOut #minstretIncLsb >});

      LETC stAddrTrunc <- TruncLsbTo (Xlen - MshwmAlign) _ #resAddrVal;
      LETC mshwmUpdCond <- (#stAddrTrunc >= mshwmb) && (#stAddrTrunc < mshwm);

      LETC newMshwm : Bit (Xlen - MshwmAlign) <- caseDefault
                                                   [(!#isException && #isCsr && #immVal == GetCsrIdx Mshwm,
                                                      TruncLsbTo (Xlen - MshwmAlign) _ #csrOut);
                                                    (!#isException && Store && #mshwmUpdCond, #stAddrTrunc) ]
                                                   mshwm;

      LETC newMshwmb : Bit (Xlen - MshwmAlign) <- ITE (!#isException && #isCsr && #immVal == GetCsrIdx Mshwmb)
                                                    (TruncLsbTo (Xlen - MshwmAlign) _ #csrOut)
                                                    mshwmb;

      LETC ieBitSet <- unpack Bool (TruncMsbTo 1 (IeBit - 1) (TruncLsbTo IeBit (Xlen - IeBit) #csrOut));
      LETC newIe : Bool <- caseDefault [(!#isException && #isCsr && #immVal == GetCsrIdx Mstatus, #ieBitSet);
                                        (!#isException && CJalr, isInterruptEnabling #cap1OType ||
                                                                   !isInterruptDisabling #cap1OType && ie)]
                             ie;

      LETC newInterrupts : Interrupts <- STRUCT { "mei" ::= (mep || !ie && mei) ;
                                                  "mti" ::= (mtp || (!ie || mei) && mti) };

      LETC newInterrupt : Bool <- ie && (mei || mti);

      LETC newMcause : Bit McauseSz <- ITE (ie && mei)
                                         $Mei
                                         (ITE (ie && mti)
                                            $Mti
                                            (ITE #isException
                                               #mcauseExceptionVal
                                               (ITE (#isCsr && #immVal == GetCsrIdx Mcause)
                                                  (TruncLsbTo McauseSz _ #csrOut)
                                                  mcause)));

      LETC newMtval : Addr <- ITE #newInterrupt $0
                                (ITE #isException
                                   #mtvalExceptionVal
                                   (ITE (#isCsr && #immVal == GetCsrIdx Mtval) #csrOut mtval));

      LETC newCsrs : Csrs <- STRUCT { "mcycle" ::= #newMcycle ;
                                      "mtime" ::= #newMtime ;
                                      "minstret" ::= #newMinstret ;
                                      "mshwm" ::= #newMshwm ;
                                      "mshwmb" ::= #newMshwmb ;
                                      "ie" ::= #newIe ;
                                      "interrupt" ::= #newInterrupt ;
                                      "mcause" ::= #newMcause ;
                                      "mtval" ::= #newMtval };

      LETC isScrWrite <- CSpecialRw && isNotZero rs1IdxFixed;
      LETC newMtdc <- ITE (!#isException && #isScrWrite && rs2IdxFixed == $Mtdc) #reg1 mtdc;
      LETC newMscratchc <- ITE (!#isException && #isScrWrite && rs2IdxFixed == $Mscratchc) #reg1 mscratch;
      
      LETC newTag <- #tag1 &&
                       (isZero (TruncLsbTo NumLsb0BitsInstAddr (Xlen - NumLsb0BitsInstAddr) #val1)) &&
                       isNotSealed (#cap1 @% "oType") &&
                       #cap1 @% "perms" @% "EX";

      LETC newCap <- #reg1 @%[ "tag" <- #newTag ]
                       @%[ "ecap" <- #cap1 ]
                       @%[ "addr" <- ({< TruncMsbTo (Xlen - NumLsb0BitsInstAddr) NumLsb0BitsInstAddr
                                           #val1, $$(wzero NumLsb0BitsInstAddr) >}) ];

      LETC newMepcc <- ITE #isException
                         (STRUCT { "tag" ::= pcTag && !BoundsException;
                                   "ecap" ::= pcCap ;
                                   "addr" ::= pcVal (* + ITE0 (pcTag && !BoundsException && ECall) $(InstSz/8) *) })
                         (ITE (#isScrWrite && rs2IdxFixed == $Mepcc) #newCap mepcc);

      LETC newMtcc <- ITE (!#isException && #isScrWrite && rs2IdxFixed == $Mtcc) #newCap mtcc;

      LETC newScrs : Scrs <- STRUCT { "mtcc" ::= #newMtcc ;
                                      "mtdc" ::= #newMtdc ;
                                      "mscratchc" ::= #newMscratchc ;
                                      "mepcc" ::= #newMepcc };

      LETC res : FullECapWithTag <- STRUCT { "tag" ::= #resTag;
                                             "ecap" ::= #resCap;
                                             "addr" ::= #resVal };

      LETC stall : Bool <- Kor [ ReadReg1 && #wait1;
                                 ReadReg2 && #wait2;
                                 #isException && isNotZero (pack waits)] ;

      LETC pcNotLinkAddrTagVal : Bool <- Kor [#isException; MRet; (Branch && #branchTaken); CJal; CJalr];
      LETC pcNotLinkAddrCap : Bool <- Kor [#isException; MRet; CJalr];

      LETC newPcTag : Bool <- ITE #isException
                                (mtcc @% "tag")
                                (caseDefault [ (MRet, mepcc @% "tag");
                                               (Branch && #branchTaken || CJal, #boundsRes);
                                               (CJalr, #tag1) ]
                                   pcTag) ;

      LETC newPcCap : ECap <- ITE #isException
                                (mtcc @% "ecap")
                                (caseDefault [ (MRet, mepcc @% "ecap");
                                               (CJalr, #cJalrAddrCap) ]
                                   pcCap) ;

      LETC newPcVal : Addr <- ITE #isException
                                (mtcc @% "addr")
                                (caseDefault [ (MRet, mepcc @% "addr");
                                               (Kor [Branch && #branchTaken; CJal; CJalr], #resAddrVal) ]
                                   #linkAddr ) ;

      LETC newPcc <- STRUCT { "tag" ::= #newPcTag ;
                              "ecap" ::= #newPcCap ;
                              "addr" ::=  #newPcVal };

      LETC newRegs : Array NumRegs FullECapWithTag <-
                       UpdateArrayConst (regs @[ #rdIdx <- ITE (WriteReg && !#isException )
                                                             #res
                                                             (regs @[ #rdIdx ]) ]) Fin.F1 #newPcc;

      LETC newWaits : Array NumRegs Bool <-
                        waits @[ #rdIdx <- MultiCycle && isNotZero #rdIdx && !#isException ];
      
      LETC ret: AluOut <- STRUCT { "regs" ::= #newRegs ;
                                   "waits" ::= #newWaits ;
                                   "csrs" ::= #newCsrs ;
                                   "scrs" ::= #newScrs ;
                                   "interrupts" ::= #newInterrupts ;
                                   "ldRegIdx" ::= #rdIdx ;
                                   "memAddr" ::= #resAddrVal ;
                                   "storeVal" ::= #reg2 ;
                                   "exception" ::= #isException ;
                                   "MRet" ::= MRet && !#isException ;
                                   "Branch" ::= Branch && !#isException ;
                                   "CJal" ::= CJal && !#isException ;
                                   "CJalr" ::= CJalr && !#isException ;
                                   "LoadUnsigned" ::= LoadUnsigned ;
                                   "memSz" ::= memSz ;
                                   "pcNotLinkAddrTagVal" ::= #pcNotLinkAddrTagVal ;
                                   "pcNotLinkAddrCap" ::= #pcNotLinkAddrCap ;
                                   "stall" ::= #stall ;
                                   "Load" ::= Load && isNotZero #rdIdx && !#isException ;
                                   "Store" ::= Store && !#isException ;
                                   "FenceI" ::= FenceI && !#isException };
      RetE #ret ).
End Alu.
