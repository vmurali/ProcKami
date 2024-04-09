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
Definition CsrIdSz := Imm12Sz.

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

Definition SoftwareInterrupt   := 3.
Definition TimerInterrupt      := 7.
Definition ExternalInterrupt   := 11.

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

Section SubsetPerms.
  Variable ty: Kind -> Type.
  Local Open Scope kami_expr.
  Definition isSubsetPerms ty (p1 p2: CapPerms @# ty) (* p1 is a subset of p2 *) :=
    (pack p1 .& pack p2) == pack p1.
End SubsetPerms.

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

Inductive RegName :=
| x0
| x1
| x2
| x3
| x4
| x5
| x6
| x7
| x8
| x9
| x10
| x11
| x12
| x13
| x14
| x15
| x16
| x17
| x18
| x19
| x20
| x21
| x22
| x23
| x24
| x25
| x26
| x27
| x28
| x29
| x30
| x31
| c0
| c1
| c2
| c3
| c4
| c5
| c6
| c7
| c8
| c9
| c10
| c11
| c12
| c13
| c14
| c15
| c16
| c17
| c18
| c19
| c20
| c21
| c22
| c23
| c24
| c25
| c26
| c27
| c28
| c29
| c30
| c31
| zero
| ra
| sp
| gp
| tp
| t0
| t1
| t2
| s0
| fp
| s1
| a0
| a1
| a2
| a3
| a4
| a5
| a6
| a7
| s2
| s3
| s4
| s5
| s6
| s7
| s8
| s9
| s10
| s11
| t3
| t4
| t5
| t6
| czero
| cra
| csp
| cgp
| ctp
| ct0
| ct1
| ct2
| cs0
| cfp
| cs1
| ca0
| ca1
| ca2
| ca3
| ca4
| ca5
| ca6
| ca7
| cs2
| cs3
| cs4
| cs5
| cs6
| cs7
| cs8
| cs9
| cs10
| cs11
| ct3
| ct4
| ct5
| ct6.

Definition getRegIdZ (name: RegName) : Z :=
  match name with
  | x0 => 0
  | x1 => 1
  | x2 => 2
  | x3 => 3
  | x4 => 4
  | x5 => 5
  | x6 => 6
  | x7 => 7
  | x8 => 8
  | x9 => 9
  | x10 => 10
  | x11 => 11
  | x12 => 12
  | x13 => 13
  | x14 => 14
  | x15 => 15
  | x16 => 16
  | x17 => 17
  | x18 => 18
  | x19 => 19
  | x20 => 20
  | x21 => 21
  | x22 => 22
  | x23 => 23
  | x24 => 24
  | x25 => 25
  | x26 => 26
  | x27 => 27
  | x28 => 28
  | x29 => 29
  | x30 => 30
  | x31 => 31
  | c0 => 0
  | c1 => 1
  | c2 => 2
  | c3 => 3
  | c4 => 4
  | c5 => 5
  | c6 => 6
  | c7 => 7
  | c8 => 8
  | c9 => 9
  | c10 => 10
  | c11 => 11
  | c12 => 12
  | c13 => 13
  | c14 => 14
  | c15 => 15
  | c16 => 16
  | c17 => 17
  | c18 => 18
  | c19 => 19
  | c20 => 20
  | c21 => 21
  | c22 => 22
  | c23 => 23
  | c24 => 24
  | c25 => 25
  | c26 => 26
  | c27 => 27
  | c28 => 28
  | c29 => 29
  | c30 => 30
  | c31 => 31
  | zero => 0
  | ra => 1
  | sp => 2
  | gp => 3
  | tp => 4
  | t0 => 5
  | t1 => 6
  | t2 => 7
  | s0 => 8
  | fp => 8
  | s1 => 9
  | a0 => 10
  | a1 => 11
  | a2 => 12
  | a3 => 13
  | a4 => 14
  | a5 => 15
  | a6 => 16
  | a7 => 17
  | s2 => 18
  | s3 => 19
  | s4 => 20
  | s5 => 21
  | s6 => 22
  | s7 => 23
  | s8 => 24
  | s9 => 25
  | s10 => 26
  | s11 => 27
  | t3 => 28
  | t4 => 29
  | t5 => 30
  | t6 => 31
  | czero => 0
  | cra => 1
  | csp => 2
  | cgp => 3
  | ctp => 4
  | ct0 => 5
  | ct1 => 6
  | ct2 => 7
  | cs0 => 8
  | cfp => 8
  | cs1 => 9
  | ca0 => 10
  | ca1 => 11
  | ca2 => 12
  | ca3 => 13
  | ca4 => 14
  | ca5 => 15
  | ca6 => 16
  | ca7 => 17
  | cs2 => 18
  | cs3 => 19
  | cs4 => 20
  | cs5 => 21
  | cs6 => 22
  | cs7 => 23
  | cs8 => 24
  | cs9 => 25
  | cs10 => 26
  | cs11 => 27
  | ct3 => 28
  | ct4 => 29
  | ct5 => 30
  | ct6 => 31
  end.

Definition isSameReg (a b: RegName) : bool :=
  Z.eqb (getRegIdZ a) (getRegIdZ b).

Definition getRegId (name: RegName) : word RegIdSz :=
  ZToWord _ (getRegIdZ name).

Definition getRegNameOpt (id: Z): option RegName :=
  match id with
  | 0%Z => Some c0
  | 1%Z => Some c1
  | 2%Z => Some c2
  | 3%Z => Some c3
  | 4%Z => Some c4
  | 5%Z => Some c5
  | 6%Z => Some c6
  | 7%Z => Some c7
  | 8%Z => Some c8
  | 9%Z => Some c9
  | 10%Z => Some c10
  | 11%Z => Some c11
  | 12%Z => Some c12
  | 13%Z => Some c13
  | 14%Z => Some c14
  | 15%Z => Some c15
  | 16%Z => Some c16
  | 17%Z => Some c17
  | 18%Z => Some c18
  | 19%Z => Some c19
  | 20%Z => Some c20
  | 21%Z => Some c21
  | 22%Z => Some c22
  | 23%Z => Some c23
  | 24%Z => Some c24
  | 25%Z => Some c25
  | 26%Z => Some c26
  | 27%Z => Some c27
  | 28%Z => Some c28
  | 29%Z => Some c29
  | 30%Z => Some c30
  | 31%Z => Some c31
  | _ => None
  end.

Definition getRegName (id: Z) := forceOption _ _ (getRegNameOpt id) tt.


Inductive ScrName :=
| scr0
| mtcc
| mtdc
| mscratchc
| mepcc.

Definition getScrIdZ (name: ScrName) : Z :=
  match name with
  | scr0 => 0
  | mtcc => 28
  | mtdc => 29
  | mscratchc => 30
  | mepcc => 31
end.

Definition isSameScr (a b: ScrName) : bool :=
  Z.eqb (getScrIdZ a) (getScrIdZ b).

Definition getScrId (name: ScrName) : word ScrIdSz :=
  ZToWord _ (getScrIdZ name).

Definition getScrNameOpt (id: Z): option ScrName :=
  match id with
  | 28%Z => Some mtcc
  | 29%Z => Some mtdc
  | 30%Z => Some mscratchc
  | 31%Z => Some mepcc
  | _ => None
  end.

Definition getScrName (id: Z) := forceOption _ _ (getScrNameOpt id) tt.

Inductive CsrName :=
| csr0
| mstatus
| mie
| mcause
| mtval.

Definition getCsrIdN (name: CsrName) : N :=
  match name with
  | csr0 => hex "0"
  | mstatus => hex "300"
  | mie => hex "304"
  | mcause => hex "342"
  | mtval => hex "343"
  end.

Definition isSameCsr (a b: CsrName) :=
  N.eqb (getCsrIdN a) (getCsrIdN b).

Definition getCsrIdZ (name: CsrName) : Z := Z.of_N (getCsrIdN name).

Definition getCsrId (name: CsrName) : word CsrIdSz := NToWord _ (getCsrIdN name).

Definition getCsrNameOpt (id: Z): option CsrName :=
  match id with
  | 768%Z => Some mstatus
  | 772%Z => Some mie
  | 834%Z => Some mcause
  | 835%Z => Some mtval
  | _ => None
  end.

Definition getCsrName (id: Z) := forceOption _ _ (getCsrNameOpt id) tt.
