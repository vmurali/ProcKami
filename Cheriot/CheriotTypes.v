Require Import Kami.AllNotations ProcKami.Cheriot.Lib.
Require Import RecordUpdate.RecordUpdate.

Definition compressed := false.

Inductive Extension := Base | M.
Definition supportedExts := [Base].

Definition RegIdSz := 5.
Definition NumRegs := Nat.pow 2 RegIdSz.
Definition RegFixedIdSz := 5.

Definition CapRSz := 1.
Definition CapOTypeSz := 3.
Definition CapPermSz := 6.
Definition CapESz := 4.
Definition CapBTSz := 9.

Definition Xlen := 32.
Definition AddrSz := Xlen.
Definition Data := Bit Xlen.
Definition Addr := Bit AddrSz.
Definition LgAddrSz := Nat.log2_up AddrSz.

Definition InstSz := 32.
Definition CompInstSz := 16.

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

Definition imm12   := [(0, Imm12Sz)].
Definition imm5    := [(0, 5)].
Definition imm20_U := [(12, Imm20Sz)].
Definition imm20_J := [(12, 8); (11, 1); (1, 10); (20, 1)].
Definition imm6    := [(0, 6)].
Definition imm7    := [(5, 7)].
Definition imm5_B  := [(11, 1); (1, 4)].
Definition imm7_B  := [(5, 6); (12, 1)].

Definition ScrIdSz := 5.

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

Section Fields.
  Variable ty: Kind -> Type.
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
End Fields.

Notation mtcc := 28%Z.
Notation mtdc := 29%Z.
Notation mscratchc := 30%Z.
Notation mepcc := 31%Z.

Notation mstatus := (Z.of_N (hex "300")).
Notation mie := (Z.of_N (hex "304")).
Notation mcause := (Z.of_N (hex "342")).
Notation mtval := (Z.of_N (hex "343")).

Definition Cap : Kind :=
  (STRUCT_TYPE {
       "R" :: Bit CapRSz;
       "p" :: Bit CapPermSz;
       "oType" :: Bit CapOTypeSz;
       "E" :: Bit CapESz;
       "T" :: Bit CapBTSz;
       "B" :: Bit CapBTSz })%kami_expr.

Definition CapSz := size Cap.

Goal CapSz = Xlen.
Proof.
  reflexivity.
Qed.

Definition NumBanks := (Xlen + CapSz) / 8.

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

Definition FullCapWithTag := STRUCT_TYPE { "tag" :: Bool ;
                                           "cap" :: Cap ;
                                           "val" :: Data }.

Definition FullCap := STRUCT_TYPE { "cap" :: Cap ;
                                    "val" :: Data }.

Definition MaxExp := AddrSz - CapBTSz - 1.

Section CapHelpers.
  Variable ty: Kind -> Type.
  Local Open Scope kami_expr.
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

  Definition encodePerms (perms: CapPerms @# ty) : Bit CapPermSz @# ty :=
    {< pack (perms @% "GL"),
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
                                   pack (perms @% "US") >})))))%kami_expr >}.

  Definition getCapExpFromE (E: Bit CapESz @# ty) : Bit LgAddrSz @# ty :=
    ITE (E == Const ty (wones _)) $MaxExp (ZeroExtend _ E).
  
  Definition getCapEFromExp (exp: Bit LgAddrSz @# ty) : Bit CapESz @# ty :=
    ITE (exp >= $(Nat.pow 2 CapESz - 1)) $$(wones CapESz) (UniBit (TruncLsb CapESz _) exp).

  Definition getCapOTypeFromIe ie: Bit CapOTypeSz @# ty := ITE ie $2 $3.

  Definition isCapSealAddr (addr: Addr @# ty) isExec := ITE isExec
                                                          (((addr >= $1) && (addr <= $3)) || addr == $6 || addr == $7)
                                                          ((addr >= $9) && (addr <= $15)).

  Definition getCapBounds (base: Bit AddrSz @# ty) (length: Bit AddrSz @# ty) :=
    ( LETC top : Bit (AddrSz + 1) <- ZeroExtend 1 base + ZeroExtend 1 length;
      LETC expInit : Bit LgAddrSz <-
                       $(AddrSz - CapBTSz) - (countLeadingZeros _ (UniBit (TruncMsb (AddrSz - CapBTSz) _) length));
      LETC isInitSatExpInitSat : Pair Bool (Bit LgAddrSz) <-
                                   ITE (#expInit > $(Nat.pow 2 CapESz - 2)) (STRUCT { "fst" ::= $$true;
                                                                                      "snd" ::= $MaxExp })
                                     (STRUCT { "fst" ::= $$false; "snd" ::= #expInit });
      LETC isInitSat <- #isInitSatExpInitSat @% "fst";
      LETC expInitSat <- #isInitSatExpInitSat @% "snd";
      LETC lostTopInit <- isNotZero (#top << ($AddrSz - #expInitSat));
      LETC lengthShifted <- UniBit (TruncLsb CapBTSz _) (length >> #expInitSat);
      LETC lengthShiftedAllOnes <- isAllOnes #lengthShifted;
      LETC exp : Bit LgAddrSz <- ITE (#lostTopInit && #lengthShiftedAllOnes && !#isInitSat)
                                   (#expInitSat + $1) (#expInitSat);
      LETC B <- UniBit (TruncLsb CapBTSz _) (base >> #exp);
      LETC lostTop <- isNotZero (#top << ($AddrSz - #exp));
      LETC TInit <- UniBit (TruncLsb CapBTSz _) (#top >> #exp);
      LETC T <- ITE #lostTop (#TInit + $1) #TInit;
      LETC lostBase <- isNotZero (base << ($AddrSz - #exp));
      RetE (STRUCT {
                "B" ::= #B;
                "T" ::= #T;
                "exp" ::= #exp;
                "exact?" ::= (#lostBase || #lostTop) } : STRUCT_TYPE { "B" :: Bit CapBTSz;
                                                                       "T" :: Bit CapBTSz;
                                                                       "exp" :: Bit LgAddrSz;
                                                                       "exact?" :: Bool } @# ty)).

  Definition getBaseTop (B T: Bit CapBTSz @# ty) (E: Bit CapESz @# ty) (addr: Addr @# ty) :=
    ( LETC exp <- getCapExpFromE E;
      LETC aMidTop <- addr >> #exp;
      LETC aMid <- UniBit (TruncLsb CapBTSz (AddrSz - CapBTSz)) #aMidTop;
      LETC aTop <- UniBit (TruncMsb CapBTSz (AddrSz - CapBTSz)) #aMidTop;
      LETC aHi <- ITE (#aMid < B) $1 $0;
      LETC tHi <- ITE (T < B) $1 $0;
      LETC aTopBase <- #aTop - #aHi;
      LETC aTopTop <- (ZeroExtend 1 #aTopBase) + #tHi;
      LETC base: Addr <- ZeroExtend _ ({< #aTopBase, B >}) << #exp;
      LETC top: Bit (AddrSz + 1) <- ZeroExtend _ ({< #aTopTop, T >}) << #exp;
      RetE (STRUCT {
                "base" ::= #base;
                "top" ::= #top;
                "aTopBase" ::= #aTopBase } : (STRUCT_TYPE { "base" :: Bit AddrSz ;
                                                            "top"  :: Bit (AddrSz + 1) ;
                                                            "aTopBase" :: Bit (AddrSz - CapBTSz) }) @# ty) ).

  Section GivenCap.
    Variable cap: Cap @# ty.
    
    Definition isCapSealed := isNotZero (cap @% "oType").
    Definition isCapSentry := (cap @% "oType" >= $1) && (cap @% "oType" <= $3).
    Definition isCapIeSentry := (cap @% "oType" == $2).
    Definition isCapIdSentry := (cap @% "oType" == $3).

    Definition sealCap (val: Bit CapOTypeSz @# ty) := cap @%[ "oType" <- val ] : Cap @# ty.
    Definition unsealCap := cap @%[ "oType" <- Const ty (wzero CapOTypeSz) ] : Cap @# ty.

    Definition getCapPerms : CapPerms @# ty := decodePerms (unpack (Array CapPermSz Bool) (cap @% "p")).
  End GivenCap.

  Definition getCapBaseTop (cap: FullCap @# ty) :=
    getBaseTop (cap @% "cap" @% "B") (cap @% "cap" @% "T") (cap @% "cap" @% "E") (cap @% "val").
  
  Definition representableFnCap (cap: FullCap @# ty) (addr: Addr @# ty) : Bool ## ty :=
    ( LETE baseTop <- getBaseTop (cap @% "cap" @% "B") (cap @% "cap" @% "T") (cap @% "cap" @% "E") (cap @% "val");
      LETE baseTop2 <- getBaseTop (cap @% "cap" @% "B") (cap @% "cap" @% "T") (cap @% "cap" @% "E") addr;
      RetE ((#baseTop @% "aTopBase") == (#baseTop2 @% "aTopBase")) ).
End CapHelpers.
