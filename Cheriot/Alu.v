Require Import Kami.All.

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
Definition NumRegs := Nat.pow 2 RegIdSz.
Definition RegFixedIdSz := 5.

Definition Imm12Sz := 12.
Definition Imm20Sz := 20.
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

Definition CsrIdSz := Imm12Sz.
Definition CsrId := Bit CsrIdSz.

Definition CapPermSz := 6.
Definition CapOTypeSz := 3.
Definition CapcMSz := 8.
Definition CapBSz := CapcMSz + 1.
Definition CapMSz := CapBSz.

Definition IeBit := 4.

Definition Cap : Kind :=
  (STRUCT_TYPE {
       "R" :: Bool;
       "p" :: Array CapPermSz Bool;
       "oType" :: Bit CapOTypeSz;
       "cE" :: Bit ExpSz;
       "cM" :: Bit CapcMSz;
       "B" :: Bit CapBSz })%kami_expr.

Definition DXlen := Eval compute in Xlen + Xlen.
Definition MemSzSz := Eval compute in Nat.log2_up (Nat.log2_up (DXlen/8)).
Definition FullCapSz := Eval compute in Xlen + size Cap.
Definition NumBytesFullCapSz := Eval compute in (FullCapSz/8).
Definition LgNumBytesFullCapSz := Eval compute in lgCeil NumBytesFullCapSz.

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
    Definition ECallException := 8.
    Definition CapException := 28.
  End Exceptions.

  Section Csr.
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
  End Csr.

  Section Scr.
    Definition Mtcc := 28.
    Definition Mtdc := 29.
    Definition Mscratchc := 30.
    Definition Mepcc := 31.
  End Scr.

  Section Sealed.
    Definition unsealed : Bit CapOTypeSz @# ty := $0.
    Section testOType.
      Variable otype: Bit CapOTypeSz @# ty.
      Definition isSealed := isNotZero otype.
      Definition isNotSealed := isZero otype.
      Definition isForwardSentry := otype == $1 || otype == $2 || otype == $3.
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

Section Fields.
  Context {ty: Kind -> Type}.
  Variable inst: Bit InstSz @# ty.

  Local Open Scope kami_expr.

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
  Definition c0Fixed : Bit RegFixedIdSz @# ty := $0.
  Definition raFixed : Bit RegFixedIdSz @# ty := $1.

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

Section Alu.
  Variable     ty: Kind -> Type.

  Variable  pcCap: ECap @# ty.
  Variable  pcVal: Addr @# ty.
  Variable   inst: Inst @# ty.
  Variable   tag1: Bool @# ty.
  Variable   cap1: ECap @# ty.
  Variable   val1: Data @# ty.
  Variable   tag2: Bool @# ty.
  Variable   cap2: ECap @# ty.
  Variable   val2: Data @# ty.
  Variable     ie: Bool @# ty.

  Variable            memSz: Bit MemSzSz @# ty.
  
  Variable           Src1Pc: Bool @# ty. (* CJAL, BNE, BEq, BLT, BGE, BLTU, BGEU, AUIPCC *)
  Variable          InvSrc2: Bool @# ty. (* SLTI, SLTIU, Sub, SLT, SLTU, CSub, CGetLen *)
  Variable         Src2Zero: Bool @# ty. (* CSetAddr,
                                            CGetAddr, CSetHigh, CAndPerm, CClearTag, CMove, CSeal, CUnseal,
                                            CSetBounds, CSetBoundsExact, CSetBoundsRoundDown, CSetBoundsImm,
                                            CSpecialRW *)
  Variable   ZeroExtendSrc1: Bool @# ty. (* SLTIU, SRLI, SLTU, SRL, BLTU, BGEU, AUIPCC,
                                            CIncAddr, CIncAddrImm, CSetAddr *)
  Variable           Branch: Bool @# ty. (* BNE, BEq, BLT, BGE, BLTU, BGEU *)
  Variable         BranchLt: Bool @# ty. (* BLT, BLTU, BGE, BGEU *)
  Variable        BranchNeg: Bool @# ty. (* BEq, BGE, BGE, BGEU *)
  Variable              Slt: Bool @# ty. (* SLTI, SLTIU, SLT, SLTU *)
  Variable              Add: Bool @# ty. (* AddI, Add, Sub, CIncAddr, CIncAddrImm, CSetAddr, CSub *)
  Variable              Xor: Bool @# ty. (* XorI, Xor *)
  Variable               Or: Bool @# ty. (* OrI, Or,
                                            CGetAddr, CSetHigh, CAndPerm, CClearTag, CMove, CSeal, CUnseal,
                                            CSetBounds, CSetBoundsExact, CSetBoundsRoundDown, CSetBoundsImm,
                                            CSpecialRW *)
  Variable              And: Bool @# ty. (* AndI, And *)
  Variable               Sl: Bool @# ty. (* SLLI, SLL *)
  Variable               Sr: Bool @# ty. (* SRLI, SRAI, SRL, SRA *)
  Variable            Store: Bool @# ty. (* CSB, CSH, CSW, CSC *)
  Variable             Load: Bool @# ty. (* CLB, CLH, CLW, CLBU, CLHU, CLC *)
  Variable        SetBounds: Bool @# ty. (* CSetBounds, CSetBoundsExact, CSetBoundsImm, CSetBoundsRoundDown *)
  Variable   SetBoundsExact: Bool @# ty. (* CSetBoundsExact *)
  Variable     BoundsSubset: Bool @# ty. (* CBoundsRoundDown *)
  Variable  BoundsFixedBase: Bool @# ty. (* CBoundsRoundDown *)

  Variable      CChangeAddr: Bool @# ty. (* CIncAddr, CIncAddrImm, CSetAddr, AUIPCC *)
  Variable           AuiPcc: Bool @# ty.
  Variable         CGetBase: Bool @# ty.
  Variable          CGetTop: Bool @# ty.
  Variable          CGetLen: Bool @# ty.
  Variable         CGetPerm: Bool @# ty.
  Variable         CGetType: Bool @# ty.
  Variable          CGetTag: Bool @# ty.
  Variable         CGetHigh: Bool @# ty.
  Variable             Cram: Bool @# ty.
  Variable             Crrl: Bool @# ty.
  Variable        CSetEqual: Bool @# ty.
  Variable      CTestSubset: Bool @# ty.
  Variable         CAndPerm: Bool @# ty.
  Variable        CClearTag: Bool @# ty.
  Variable         CSetHigh: Bool @# ty.
  Variable            CMove: Bool @# ty.
  Variable            CSeal: Bool @# ty.
  Variable          CUnseal: Bool @# ty.
  
  Variable    SignExtendImm: Bool @# ty. (* AddI, SLTI, XorI, OrI, AndI, CIncAddrImm,
                                            CLB, CLH, CLW, CLBU, CLHU, CLC, CJALR *)
  Variable    ZeroExtendImm: Bool @# ty. (* SLTIU, CSetBoundsImm, SLLI, SRLI, SRAI *)
  Variable             CJal: Bool @# ty.
  Variable            CJalr: Bool @# ty.
  Variable           AuiImm: Bool @# ty. (* AUIPCC, AUICGP *)
  Variable              Lui: Bool @# ty.

  Variable       CSpecialRw: Bool @# ty.
  Variable             MRet: Bool @# ty.
  Variable            ECall: Bool @# ty.
  Variable           EBreak: Bool @# ty.
  Variable          Illegal: Bool @# ty.

  Variable            CsrRw: Bool @# ty. (* CSRRW, CSRRWI *)
  Variable           CsrSet: Bool @# ty. (* CSRRS, CSRRSI *)
  Variable         CsrClear: Bool @# ty. (* CSRRC, CSRRCI *)
  Variable           CsrImm: Bool @# ty. (* CSRRWI, CSRRSI, CSRRCI; rs1 field *)

  Variable  BoundsException: Bool @# ty.
  Variable     TagException: Bool @# ty.
  
  Local Open Scope kami_expr.
  Local Notation ITE0 x y := (ITE x y (Const ty Default)).
  Local Notation GetCsrIdx x := $$(NToWord CsrIdSz x).

  Definition signExtendImm: Bit (Xlen + 1) @# ty := SignExtendTo (Xlen + 1) (imm inst).
  Definition zeroExtendImm: Bit (Xlen + 1) @# ty := ZeroExtendTo (Xlen + 1) (imm inst).
  Definition         stImm: Bit (Xlen + 1) @# ty := SignExtendTo (Xlen + 1) ({< funct7 inst, rdFixed inst >}).
  Definition     branchImm: Bit (Xlen + 1) @# ty := SignExtendTo (Xlen + 1) (branchOffset inst).
  Definition        jalImm: Bit (Xlen + 1) @# ty := SignExtendTo (Xlen + 1) (jalOffset inst).
  Definition        auiImm: Bit (Xlen + 1) @# ty := SignExtendTo (Xlen + 1) ({< auiLuiOffset inst, $$(wzero 11) >}).
  Definition        luiImm: Bit Xlen @# ty := SignExtendTo Xlen ({< auiLuiOffset inst, $$(wzero 12) >}).

  Definition saturatedMax {n} (e: Bit (n + 1) @# ty) :=
    ITE (unpack Bool (TruncMsbTo 1 n e)) $$(wones n) (TruncLsbTo n 1 e).

  Definition AluRes := STRUCT_TYPE { "res" :: FullECapWithTag ;
                                     "resAddrTag" :: Bool ;
                                     "resAddrCap" :: ECap ;
                                     "resAddrVal" :: Addr ;
                                     "linkAddr" :: Addr ;
                                     "storeVal" :: FullECapWithTag ;
                                     "mcause" :: Data ;
                                     "mtval" :: Data ;
                                     "csrId" :: CsrId ;
                                     "scrId" :: Bit RegFixedIdSz ;
                                     "memSz" :: Bit MemSzSz ;
                                     "ie" :: Bool ;
                                     "branch" :: Bool ;
                                     "branchTaken" :: Bool ;
                                     "cjal" :: Bool ;
                                     "cjalr" :: Bool ;
                                     "redirectPcVal" :: Bool ;
                                     "redirectPcCap" :: Bool ;
                                     "ld" :: Bool ;
                                     "st" :: Bool ;
                                     "csr" :: Bool ;
                                     "scr" :: Bool ;
                                     "csrScrWrite" :: Bool ;
                                     "csrRw" :: Bool ;
                                     "csrSet" :: Bool ;
                                     "csrClear" :: Bool ;
                                     "updIe" :: Bool ;
                                     "mRet" :: Bool ;
                                     "resValid" :: Bool ;
                                     "fetchException" :: Bool ;
                                     "exception" :: Bool }.
             
  Local Definition exception x := (STRUCT { "valid" ::= $$true;
                                            "data" ::= x } : Maybe (Bit CapExceptSz) @# ty ).

  Definition alu : AluRes ## ty :=
    ( LETC signExtImm <- ITE0 SignExtendImm signExtendImm;

      LETC cap1Base <- cap1 @% "base";
      LETC cap1Top <- cap1 @% "top";
      LETC cap1Perms <- cap1 @% "perms";
      LETC cap1OType <- cap1 @% "oType";
      LETC cap2Base <- cap2 @% "base";
      LETC cap2Top <- cap2 @% "top";
      LETC cap2Perms <- cap2 @% "perms";
      LETC cap2OType <- cap2 @% "oType";
      LETC cap1NotSealed <- isNotSealed #cap1OType;
      LETC cap2NotSealed <- isNotSealed #cap2OType;

      LETC rdIdx <- rdFixed inst;
      LETC rs1Idx <- rs1Fixed inst;
      LETC rs2Idx <- rs2Fixed inst;
      LETC immVal <- imm inst;

      LETC src1 <- ITE Src1Pc pcVal val1;
      LETC src2Full <- Kor [ #signExtImm; ITE0 ZeroExtendImm zeroExtendImm; ITE0 AuiImm auiImm;
                             SignExtend 1 (ITE0 (!Src2Zero) val2)];
      LETC adderSrc1 <- Kor [ ITE0 CGetLen #cap1Top;
                              ITE ZeroExtendSrc1 (ZeroExtend 1 #src1) (SignExtend 1 #src1) ];
      LETC adderSrc2 <- Kor [ ITE0 CGetLen #cap1Base; #src2Full ];
      LETC adderSrc2Fixed <- ITE InvSrc2 (~#adderSrc2) #adderSrc2;
      LETC carryExt  <- ZeroExtend Xlen (pack InvSrc2);
      LETC adderResFull <- #adderSrc1 + #adderSrc2Fixed + #carryExt;
      LETC adderResNotZero <- isNotZero #adderResFull;
      LETC adderCarryBool <- unpack Bool (TruncMsbTo 1 Xlen #adderResFull);
      LETC branchTakenPos <- ITE BranchLt #adderCarryBool #adderResNotZero;
      LETC branchTaken <- BranchNeg ^^ #branchTakenPos;
      LETC adderRes: Data <- TruncLsbTo Xlen 1 #adderResFull;
      LETC src2 <- TruncLsbTo Xlen 1 #src2Full;
      LETC xorRes <- val1 .^ #src2;
      LETC orRes <- val1 .| #src2;
      LETC andRes <- val1 .& #src2;
      LETC shiftAmt <- TruncLsbTo (Nat.log2_up Xlen) _ #src2;
      LETC slRes <- val1 << #shiftAmt;
      LETC srRes <- TruncLsbTo Xlen 1 (#adderSrc1 >>> #shiftAmt);

      LETC addrImmVal <- Kor [ #signExtImm; ITE0 Branch branchImm; ITE0 CJal jalImm; ITE0 Store stImm;
                               ITE0 CSpecialRw $0 ];
      LETC resAddrValFullTemp <- (ZeroExtend 1 #src1) + #addrImmVal;
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

      LETC baseCheckBase <- Kor [ ITE0 Src1Pc (pcCap @% "base"); ITE0 #seal_unseal #cap2Base; #cap1Base ];
      LETC baseCheckAddr <- Kor [ ITE0 CSeal (ZeroExtend 1 val2); ITE0 CUnseal (ZeroExtendTo (Xlen + 1) #cap1OType);
                                  ITE0 #branch_jump_load_store # resAddrValFull;
                                  ITE0 CTestSubset #cap2Base;
                                  #adderResFull ];
      LETC baseCheck <- (#baseCheckBase <= #baseCheckAddr) &&
                          (!#change_addr || !(unpack Bool (TruncMsbTo 1 Xlen #baseCheckAddr)));

      LETC representableLimit <- getRepresentableLimit
                                   (ITE Src1Pc (pcCap @% "base") #cap1Base)
                                   (get_ECorrected_from_E (ITE Src1Pc (pcCap @% "E") (cap1 @% "E")));
      LETC topCheckTop <- Kor [ ITE0 #seal_unseal #cap2Top;
                                ITE0 (#branch_jump || CChangeAddr) #representableLimit;
                                #cap1Top ];
      LETC topCheckAddr <-  Kor [ ITE0 CSeal (ZeroExtend 1 val2);
                                  ITE0 CUnseal (ZeroExtendTo (Xlen + 1) #cap1OType);
                                  ITE0 #branch_jump_load_store #resAddrValFull;
                                  ITE0 CTestSubset #cap2Top;
                                  #adderResFull ];
      LETC addrPlus <- Kor [ITE0 #load_store ($1 << memSz); ZeroExtend Xlen (pack (!CTestSubset))];
      LETC topCheckAddrFinal <- #topCheckAddr + #addrPlus;
      LETC topCheck <-
        (#topCheckAddrFinal <= #topCheckTop) &&
          (!(#change_addr || CSeal || CUnseal) ||
             (!(unpack Bool (TruncMsbTo 1 Xlen #topCheckAddrFinal)) ||
                isZero (TruncLsbTo Xlen 1 #topCheckAddrFinal)));

      LETC boundsRes <- #baseCheck && #topCheck;
      
      LETC cTestSubset <- tag1 == tag2 && #boundsRes && ((pack #cap1Perms .& pack #cap2Perms) == pack #cap2Perms);

      LETE encodedCap <- encodeCap cap1;
      LETC cram_crrl <- Cram || Crrl;
      LETC boundsBase <- ZeroExtend 1 (ITE #cram_crrl $0 val1);
      LETC boundsLength <- ZeroExtend 1 (ITE #cram_crrl val1 val2);
      LETE newBounds <- calculateBounds #boundsBase #boundsLength BoundsSubset BoundsFixedBase;
      LETC newBoundsTop <- #newBounds @% "base" + #newBounds @% "length";
      LETC cSetEqual <- tag1 == tag2 && cap1 == cap2 && val1 == val2;
      LETC zeroExtendBoolRes <- ZeroExtendTo Xlen (pack (Kor [ITE0 Slt #adderCarryBool;
                                                              ITE0 CGetTag tag1;
                                                              ITE0 CSetEqual #cSetEqual;
                                                              ITE0 CTestSubset #cTestSubset]));

      LETC cAndPermMask <- TruncLsbTo (size CapPerms) (Xlen - size CapPerms) val2;
      LETC cAndPermCapPerms <- unpack CapPerms (pack #cap1Perms .& #cAndPermMask);
      LETC cAndPermCap <- cap1 @%[ "perms" <- #cAndPermCapPerms];
      LETC cAndPermTagNew <- (#cap1NotSealed ||
                                isAllOnes (pack ((unpack CapPerms (#cAndPermMask)) @%[ "GL" <- $$true ])));

      LETE cSetHighCap <- decodeCap (unpack Cap val2) val1;

      LETC cChangeAddrTagNew <- (Src1Pc || #cap1NotSealed) && #boundsRes;

      LETC cSealCap <- cap1 @%[ "oType" <- TruncLsbTo CapOTypeSz (AddrSz - CapOTypeSz) val2];
      LETC cSealTagNew <- tag2 && #cap1NotSealed && #cap2NotSealed && (#cap2Perms @% "SE") && #boundsRes &&
                            isSealableAddr (#cap1Perms @% "EX") val1;

      LETC cUnsealCap <- cap1 @%[ "oType" <- @unsealed ty ]
                           @%[ "perms" <- #cap1Perms @%[ "GL" <- #cap1Perms @% "GL" && #cap2Perms @% "GL" ] ];
      LETC cUnsealTagNew <- tag2 && !#cap1NotSealed && #cap2NotSealed && (#cap2Perms @% "US") && #boundsRes;

      LETC cSetBoundsCap <- cap1 @%[ "E" <- #newBounds @% "E" ]
                              @%[ "top" <- #newBoundsTop ]
                              @%[ "base" <- #newBounds @% "base" ];

      LETC cJalJalrCap <- pcCap @%[ "oType" <- ITE0 (#rdIdx == raFixed) (createBackwardSentry ie) ];
      LETC cJalrAddrCap <- cap1 @%[ "oType" <- unsealed ty];
      LETC newIe <- ((CJalr && isInterruptEnabling #cap1OType) ||
                       (ie && !(CJalr && isInterruptDisabling #cap1OType)));
      LETC notSealedOrInheriting <- #cap1NotSealed || isInterruptInheriting #cap1OType;
      LETC cJalrSealedCond <-
        (ITE (#rdIdx == c0Fixed)
           (ITE (#rs1Idx == raFixed) (isBackwardSentry #cap1OType) #notSealedOrInheriting)
           (ITE (#rdIdx == raFixed) (#cap1NotSealed || isForwardSentry #cap1OType) #notSealedOrInheriting));

      LETC isCsr <- CsrRw || CsrSet || CsrClear;

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

      LETC capSrException <- (CSpecialRw || MRet || (#isCsr && #validCsr))
                             && !(pcCap @% "perms" @% "SR");
      LETC isCapMem <- memSz == $LgNumBytesFullCapSz;
      LETC capNotAligned <- isNotZero (TruncLsbTo LgNumBytesFullCapSz (AddrSz - LgNumBytesFullCapSz) #resAddrVal) &&
                              #isCapMem;
      LETC clcException <- Load && #capNotAligned;
      LETC cscException <- Store && #capNotAligned;

      LETC validScr <- Kor [ #rs2Idx == $Mtcc;
                             #rs2Idx == $Mtdc;
                             #rs2Idx == $Mscratchc;
                             #rs2Idx == $Mepcc ];

      LETC fullIllegal <- Kor [Illegal; #isCsr && !#validCsr; CSpecialRw && !#validScr];

      LETC capException <-
        Kor [ ITE0 #capSrException (exception $SrViolation) ;
              ITE (#load_store && !tag1) (exception $TagViolation)
                (ITE (#load_store && !#cap1NotSealed ||
                        (CJalr && (!#cJalrSealedCond || !#cap1NotSealed && isNotZero (imm inst))))
                   (exception $SealViolation)
                   (ITE ((CJalr && !(#cap1Perms @% "EX")) || (Load && !(#cap1Perms @% "LD")) ||
                           (Store && !(#cap1Perms @% "SD")))
                      (exception (Kor [ ITE0 (CJalr && !(#cap1Perms @% "EX")) $ExViolation;
                                        ITE0 (Load && !(#cap1Perms @% "LD")) $LdViolation;
                                        ITE0 (Store && !(#cap1Perms @% "SD")) $SdViolation ]))
                      (ITE (Store && #isCapMem && !(#cap1Perms @% "MC"))
                         (exception $McSdViolation)
                         (ITE0 (#load_store && !#boundsRes)
                            (exception $BoundsViolation) )))) ];

      LETC capExceptionVal <- #capException @% "data";
      LETC isCapException <- #capException @% "valid";
      LETC capExceptionSrc <- ITE0 (!#capSrException) #rs1Idx;

      LETC isException <- Kor [TagException; BoundsException;
                               #fullIllegal; EBreak; ECall; #clcException; #cscException; #isCapException];

      LETC mcauseVal: Bit Xlen <- ITE (TagException || BoundsException)
                                    $CapException
                                    (ITE (#isException && !#isCapException)
                                       (Kor [ ITE0 #fullIllegal $IllegalException;
                                              ITE0 EBreak $EBreakException;
                                              ITE0 ECall $ECallException;
                                              ITE0 #clcException $LdAlignException;
                                              ITE0 #cscException $SdAlignException ])
                                       (ITE0 #isCapException $CapException));

      LETC mtvalVal: Bit Xlen <- ITE (TagException || BoundsException)
                                   (@ZeroExtendTo _ Xlen CapExceptSz (Kor [ITE0 TagException $TagViolation;
                                                                           ITE0 BoundsException $BoundsViolation]))
                                   (ITE (#isException && !#isCapException)
                                      (Kor [ ITE0 #fullIllegal inst;
                                             ITE0 (#clcException || #cscException) #resAddrVal ])
                                      (ITE0 #isCapException
                                         (ZeroExtendTo Xlen ({< #capExceptionSrc, #capExceptionVal >}))));

      LETC saturated <- saturatedMax
                          (Kor [ITE0 CGetBase #cap1Base; ITE0 CGetTop #cap1Top; ITE0 CGetLen #adderResFull;
                                ITE0 Crrl (#newBounds @% "length") ]);

      LETC linkAddr <- pcVal + if HasComp then $(InstSz/8) else ITE (isCompressed inst) $(InstSz/8) $(CompInstSz/8);

      LETC csrWrite <- ITE CsrImm (ZeroExtendTo Xlen #rs1Idx) val1;

      LETC resVal <- Kor [ ITE0 Add #adderRes; ITE0 Lui luiImm;
                           ITE0 Xor #xorRes; ITE0 Or #orRes; ITE0 And #andRes;
                           ITE0 Sl #slRes; ITE0 Sr #srRes;
                           ITE0 CGetPerm (ZeroExtendTo Xlen (pack #cap1Perms));
                           ITE0 CGetType (ZeroExtendTo Xlen #cap1OType);
                           ITE0 CGetHigh (pack #encodedCap);
                           ITE0 #cjal_cjalr #linkAddr;
                           ITE0 Cram (TruncLsbTo Xlen 1 (#newBounds @% "cram"));
                           ITE0 #isCsr #csrWrite;
                           #saturated;
                           #zeroExtendBoolRes];

      LETC resTag <- (tag1 && Kor [ CAndPerm && #cAndPermTagNew;
                                    CMove;
                                    CChangeAddr && #cChangeAddrTagNew;
                                    CSeal && #cSealTagNew;
                                    ITE0 SetBounds (!SetBoundsExact || (#newBounds @% "exact"));
                                    CUnseal && #cUnsealTagNew;
                                    #cjal_cjalr;
                                    CSpecialRw ]);

      LETC resCap <- Kor [ ITE0 CAndPerm #cAndPermCap;
                           ITE0 (CClearTag || CMove || CChangeAddr || CSpecialRw) (ITE Src1Pc pcCap cap1);
                           ITE0 CSetHigh #cSetHighCap;
                           ITE0 SetBounds #cSetBoundsCap;
                           ITE0 #cjal_cjalr #cJalJalrCap;
                           ITE0 CSeal #cSealCap;
                           ITE0 CUnseal #cUnsealCap ];

      LETC ieBitSet <- unpack Bool (TruncMsbTo 1 (IeBit - 1) (TruncLsbTo IeBit (Xlen - IeBit) #csrWrite));
      LETC updIeCsr <- #isCsr && #immVal == GetCsrIdx Mstatus &&
                                              Kor [ CsrRw;
                                                    CsrSet && #ieBitSet;
                                                    CsrClear && #ieBitSet];
      LETC newIeCsr <- CsrRw && #ieBitSet || CsrSet;

      LETC res : FullECapWithTag <- STRUCT { "tag" ::= #resTag;
                                             "ecap" ::= #resCap;
                                             "addr" ::= #resVal };

      LETC ret: AluRes <- STRUCT { "res" ::= #res;
                                   "resAddrTag" ::= Kor [ ITE0 ((Branch && #branchTaken) || CJal) #boundsRes;
                                                          ITE0 CJalr tag1 ];
                                   "resAddrCap" ::= #cJalrAddrCap;
                                   "resAddrVal" ::= #resAddrVal; (* Note: has load/store address also *)
                                   "linkAddr" ::= #linkAddr;
                                   "storeVal" ::= STRUCT { "tag" ::= tag2 ;
                                                           "ecap" ::= cap2 ;
                                                           "addr" ::= val2 } ;
                                   "mcause" ::= #mcauseVal ;
                                   "mtval" ::= #mtvalVal ;
                                   "csrId" ::= #immVal ;
                                   "scrId" ::= #rs2Idx ;
                                   "memSz" ::= memSz ;
                                   "ie" ::= (#newIe || #newIeCsr);
                                   "branch" ::= Branch && !#isException;
                                   "branchTaken" ::= #branchTaken;
                                   "cjal" ::= CJal && !#isException;
                                   "cjalr" ::= CJalr && !#isException;
                                   "redirectPcVal" ::= ((Branch && #branchTaken) || #cjal_cjalr) && !#isException;
                                   "redirectPcCap" ::= CJalr && !#isException;
                                   "ld" ::= Load && !#isException;
                                   "st" ::= Store && !#isException;
                                   "csr" ::= #isCsr && !#isException;
                                   "scr" ::= CSpecialRw && !#isException;
                                   "csrScrWrite" ::= (CsrRw || isNotZero #rs1Idx);
                                   "csrRw" ::= CsrRw;
                                   "csrSet" ::= CsrSet;
                                   "csrClear" ::= CsrClear;
                                   "updIe" ::= (((isInterruptEnabling #cap1OType || isInterruptDisabling #cap1OType)
                                                 && CJalr) || #updIeCsr) && !#isException;
                                   "mRet" ::= MRet && !#isException;
                                   "resValid" ::= !(Branch || #load_store || #isCsr || CSpecialRw ||
                                                      isZero #rdIdx || #isException);
                                   "fetchException" ::= (TagException || BoundsException);
                                   "exception" ::= #isException };
      RetE #ret ).
End Alu.

(* CSRs mslwm, mshwm, performance counters *)

Section Csr.
  Variable prefix: string.
  
  Variable ty: Kind -> Type.

  Variable WriteCsr: Bool @# ty.
  Variable CsrRw: Bool @# ty.
  Variable CsrSet: Bool @# ty.
  Variable CsrClear: Bool @# ty.
  Variable UpdIe: Bool @# ty.
  Variable Exception: Bool @# ty.
  Variable IsStore: Bool @# ty.
  Variable Commit: Bool @# ty.

  Variable newIe: Bool @# ty.
  Variable csrIdx: CsrId @# ty.
  Variable updVal: Data @# ty.
  Variable newMcause: Data @# ty.
  Variable newMtval: Data @# ty.
  Variable stAddr: Addr @# ty.

  Local Open Scope kami_action.
  Local Open Scope kami_expr.

  Local Notation checkIdx idx := (csrIdx == $$(NToWord CsrIdSz idx)).
  Local Notation ITE0 x y := (ITE x y (Const ty Default)).
  Local Notation "@^ x" := (prefix ++ "_" ++ x)%string (at level 0).
  
  Definition doCsr: ActionT ty Data :=
    ( Read mcycleVal : Bit DXlen <- @^"mcycleFull";
      LET mcycleLsb : Bit Xlen <- TruncLsbTo Xlen Xlen #mcycleVal;
      LET mcycleMsb : Bit Xlen <- TruncMsbTo Xlen Xlen #mcycleVal;
      Read mtimeVal : Bit DXlen <- @^"mtimeFull";
      LET mtimeLsb : Bit Xlen <- TruncLsbTo Xlen Xlen #mtimeVal;
      LET mtimeMsb : Bit Xlen <- TruncMsbTo Xlen Xlen #mtimeVal;
      Read minstretVal : Bit DXlen <- @^"minstretFull";
      LET minstretLsb : Bit Xlen <- TruncLsbTo Xlen Xlen #minstretVal;
      LET minstretMsb : Bit Xlen <- TruncMsbTo Xlen Xlen #minstretVal;
      Read mshwmVal : Bit (Xlen - MshwmAlign) <- @^"mshwmReg";
      Read mshwmbVal : Bit (Xlen - MshwmAlign) <- @^"mshwmbReg";
      Read ieVal : Bool <- @^"ieSingle";
      Read mcauseVal : Data <- @^"mcauseReg";
      Read mtvalVal : Data <- @^"mtvalReg";

      LET ret : Data <- Kor [ ITE0 (checkIdx Mcycle) #mcycleLsb;
                              ITE0 (checkIdx Mtime) #mtimeLsb;
                              ITE0 (checkIdx Minstret) #minstretLsb;
                              ITE0 (checkIdx Mcycleh) #mcycleMsb;
                              ITE0 (checkIdx Mtimeh) #mtimeMsb;
                              ITE0 (checkIdx Minstreth) #minstretMsb;
                              ITE0 (checkIdx Mshwm) ({< #mshwmVal, $$(wzero MshwmAlign) >});
                              ITE0 (checkIdx Mshwmb) ({< #mshwmbVal, $$(wzero MshwmAlign) >});
                              ITE0 (checkIdx Mstatus) (ZeroExtendTo Xlen ({< pack #ieVal, $$(wzero (IeBit-1)) >}));
                              ITE0 (checkIdx Mcause) #mcauseVal;
                              ITE0 (checkIdx Mtval) #mtvalVal ];
      
      LET writeVal : Data <- Kor [ ITE0 CsrSet (#ret .| updVal);
                                   ITE0 CsrClear (#ret .& ~updVal);
                                   updVal ];

      Write @^"mcycleFull" : Bit DXlen <- Kor [ ITE0 (WriteCsr && checkIdx Mcycle)  ({< #mcycleMsb, #writeVal >});
                                                ITE0 (WriteCsr && checkIdx Mcycleh) ({< #writeVal, #mcycleLsb >});
                                                #mcycleVal + $1 ];

      Write @^"mtimeFull" : Bit DXlen <- Kor [ ITE0 (WriteCsr && checkIdx Mtime)  ({< #mtimeMsb, #writeVal >});
                                               ITE0 (WriteCsr && checkIdx Mtimeh) ({< #writeVal, #mtimeLsb >});
                                               #mtimeVal + $1 ];

      Write @^"minstretFull" : Bit DXlen <- Kor [ ITE0 (WriteCsr && checkIdx Minstret)
                                                    ({< #minstretMsb, #writeVal >});
                                                  ITE0 (WriteCsr && checkIdx Minstreth)
                                                    ({< #writeVal, #minstretLsb >});
                                                  #minstretVal + ZeroExtendTo DXlen (pack Commit) ] ;

      Write @^"mshwmbReg" : Bit (Xlen - MshwmAlign) <-
                              Kor [ ITE0 (WriteCsr && checkIdx Mshwmb) (TruncLsbTo (Xlen - MshwmAlign) _ #writeVal);
                                    #mshwmbVal ];

      LET stAddrTrunc <- TruncLsbTo (Xlen - MshwmAlign) _ stAddr;

      Write @^"mshwmReg" : Bit (Xlen - MshwmAlign) <-
                             Kor [ ITE0 (WriteCsr && checkIdx Mshwm) (TruncLsbTo (Xlen - MshwmAlign) _ #writeVal);
                                   ITE0 (IsStore && (#stAddrTrunc >= #mshwmbVal) && (#stAddrTrunc < #mshwmVal))
                                     #stAddrTrunc;
                                   #mshwmVal ];

      Write @^"ieSingle" : Bool <- ITE UpdIe newIe #ieVal;

      Write @^"mcauseReg" : Data <- Kor [ ITE0 Exception newMcause;
                                          ITE (WriteCsr && checkIdx Mcause) #writeVal #mcauseVal ];

      Write @^"mtvalReg" : Data <- Kor [ ITE0 Exception newMtval;
                                         ITE (WriteCsr && checkIdx Mtval) #writeVal #mcauseVal ];
      
      Ret #ret
    ).
End Csr.

Section Scr.
  Variable prefix: string.
  
  Variable ty: Kind -> Type.

  Variable WriteScr: Bool @# ty.
  Variable Exception: Bool @# ty.
  Variable FetchViolation: Bool @# ty.
  Variable MRet: Bool @# ty.

  Variable scrIdx: Bit RegFixedIdSz @# ty.
  Variable newCap: FullECapWithTag @# ty.
  Variable nextPcc: FullECapWithTag @# ty.

  Local Open Scope kami_action.
  Local Open Scope kami_expr.

  Local Notation ITE0 x y := (ITE x y (Const ty Default)).
  Local Notation "@^ x" := (prefix ++ "_" ++ x)%string (at level 0).

  Definition ScrOutput := STRUCT_TYPE { "scr" :: FullECapWithTag ;
                                        "newPcFull" :: FullECapWithTag ;
                                        "redirectPc" :: Bool }.

  Local Notation checkIdx idx := (scrIdx == $idx).
  Notation isLsbSet x := (isNotZero (TruncLsbTo NumLsb0BitsInstAddr (Xlen - NumLsb0BitsInstAddr) x)).

  Definition doScr: ActionT ty ScrOutput :=
    ( Read mtcc : FullECapWithTag <- @^"mtcc";
      Read mtdc : FullECapWithTag <- @^"mtdc";
      Read mscratchc : FullECapWithTag <- @^"mscratchc";
      Read mepcc : FullECapWithTag <- @^"mepcc";

      Read fullPc: FullECapWithTag <- @^"fullPc";

      Write @^"mtdc" <- ITE (WriteScr && checkIdx Mtdc) newCap #mtdc;

      Write @^"mscratchc" <- ITE (WriteScr && checkIdx Mscratchc) newCap #mscratchc;

      LET updTag <- newCap @% "tag" &&
                      !isLsbSet (newCap @% "addr") &&
                      isNotSealed (newCap @% "ecap" @% "oType") &&
                      newCap @% "ecap" @% "perms" @% "EX";

      LET updCap <- newCap @%[ "tag" <- #updTag ]
                      @%[ "ecap" <- newCap @% "ecap" ]
                      @%[ "addr" <- ({< TruncMsbTo (Xlen - NumLsb0BitsInstAddr) NumLsb0BitsInstAddr
                                          (newCap @% "addr"),
                                        $$(wzero NumLsb0BitsInstAddr) >}) ];

      Write @^"mepcc" <- Kor [ ITE0 Exception (STRUCT { "tag" ::= #fullPc @% "tag" && !FetchViolation;
                                                        "ecap" ::= #fullPc @% "ecap";
                                                        "addr" ::= #fullPc @% "addr" });
                               ITE (WriteScr && checkIdx Mepcc) #updCap #mepcc ];
      Write @^"mtcc" <- ITE (WriteScr && checkIdx Mtcc) #updCap #mtcc;

      LET scr: FullECapWithTag <- Kor [ ITE0 (checkIdx Mtcc) #mtcc;
                                        ITE0 (checkIdx Mtdc) #mtdc;
                                        ITE0 (checkIdx Mscratchc) #mscratchc;
                                        ITE0 (checkIdx Mepcc) #mepcc ];

      LET redirectPc <- Kor [ Exception; MRet ];

      LET newFullPc <- Kor [ ITE0 Exception #mtcc;
                             ITE0 MRet #mepcc;
                             ITE0 (!#redirectPc) nextPcc ];

      Write @^"fullPc" <- #newFullPc;

      LET ret : ScrOutput <- STRUCT { "scr" ::= #scr;
                                      "newPcFull" ::= #newFullPc;
                                      "redirectPc" ::= #redirectPc };
      
      Ret #ret ).
End Scr.
