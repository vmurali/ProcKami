Require Import Kami.AllNotations ProcKami.Cheriot.Lib ProcKami.Cheriot.Types ProcKami.Cheriot.DecExec.
Require Import RecordUpdate.RecordUpdate.

Section InstBaseSpec.
  Context `{procParams: ProcParams}.
  Local Open Scope kami_expr.

  Section ty.
    Variable ty: Kind -> Type.
    Local Definition Trunc32Signed := @TruncToSizeSigned ty 32.
    Local Definition Trunc32Unsigned := @TruncToSizeUnsigned ty 32.
    Definition DefFullOutput: FullOutput @# ty := Const _ Default.
    Definition DefWbFullOutput := DefFullOutput @%[ "wb?" <- $$true ].

  End ty.

  Definition aluInsts: InstEntryFull FullOutput.
    refine
      {|xlens := [32; 64];
        extension := Base;
        instEntries := [
          {|instName := "AddI";
            uniqId := [fieldVal opcodeField (5'b"00100");
                       fieldVal funct3Field (3'b"000")];
            immEncoder := [ Build_ImmEncoder (fst immField) imm12 ];
            spec ty pc inst cs1 cs2 scr csr :=
              ( RetE ((DefWbFullOutput ty)
                        @%[ "cdVal" <- (cs1 @% "val") + SignExtendTruncLsb Xlen (imm inst)]));
            instProperties := DefProperties<| hasCs1 := true |>;
            goodInstEncode := eq_refl;
            goodImmEncode := ltac:(eexists; cbv; eauto)
          |};
          {|instName := "SLTI";
            uniqId := [fieldVal opcodeField (5'b"00100");
                       fieldVal funct3Field (3'b"010")];
            immEncoder := [ Build_ImmEncoder (fst immField) imm12 ];
            spec ty pc inst cs1 cs2 scr csr :=
              ( LETC in1 <- SignExtend 1 (cs1 @% "val");
                LETC in2 <- SignExtendTruncLsb (Xlen + 1) (imm inst);
                LETC res <- #in1 - #in2;
                LETC msb <- UniBit (TruncMsb Xlen 1) #res;
                RetE ((DefWbFullOutput ty)
                        @%[ "cdVal" <- ZeroExtendTruncLsb Xlen #msb]));
            instProperties := DefProperties<| hasCs1 := true |>;
            goodInstEncode := eq_refl;
            goodImmEncode := ltac:(eexists; cbv; eauto)
          |};
          {|instName := "SLTIU";
            uniqId := [fieldVal opcodeField (5'b"00100");
                       fieldVal funct3Field (3'b"011")];
            immEncoder := [ Build_ImmEncoder (fst immField) imm12 ];
            spec ty pc inst cs1 cs2 scr csr :=
              ( LETC in1 <- ZeroExtend 1 (cs1 @% "val");
                LETC in2 <- ZeroExtendTruncLsb (Xlen + 1) (imm inst);
                LETC res <- #in1 - #in2;
                LETC msb <- UniBit (TruncMsb Xlen 1) #res;
                RetE ((DefWbFullOutput ty)
                        @%[ "cdVal" <- ZeroExtendTruncLsb Xlen #msb]));
            instProperties := DefProperties<| hasCs1 := true |>;
            goodInstEncode := eq_refl;
            goodImmEncode := ltac:(eexists; cbv; eauto)
          |};
          {|instName := "XorI";
            uniqId := [fieldVal opcodeField (5'b"00100");
                       fieldVal funct3Field (3'b"100")];
            immEncoder := [ Build_ImmEncoder (fst immField) imm12 ];
            spec ty pc inst cs1 cs2 scr csr :=
              ( RetE ((DefWbFullOutput ty)
                        @%[ "cdVal" <- ((cs1 @% "val") .^ (SignExtendTruncLsb Xlen (imm inst))) ]));
            instProperties := DefProperties<| hasCs1 := true |>;
            goodInstEncode := eq_refl;
            goodImmEncode := ltac:(eexists; cbv; eauto)
          |};
          {|instName := "OrI";
            uniqId := [fieldVal opcodeField (5'b"00100");
                       fieldVal funct3Field (3'b"110")];
            immEncoder := [ Build_ImmEncoder (fst immField) imm12 ];
            spec ty pc inst cs1 cs2 scr csr :=
              ( RetE ((DefWbFullOutput ty)
                        @%[ "cdVal" <- ((cs1 @% "val") .| (SignExtendTruncLsb Xlen (imm inst))) ]));
            instProperties := DefProperties<| hasCs1 := true |>;
            goodInstEncode := eq_refl;
            goodImmEncode := ltac:(eexists; cbv; eauto)
          |};
          {|instName := "AndI";
            uniqId := [fieldVal opcodeField (5'b"00100");
                       fieldVal funct3Field (3'b"111")];
            immEncoder := [ Build_ImmEncoder (fst immField) imm12 ];
            spec ty pc inst cs1 cs2 scr csr :=
              ( RetE ((DefWbFullOutput ty)
                        @%[ "cdVal" <- ((cs1 @% "val") .& (SignExtendTruncLsb Xlen (imm inst))) ]));
            instProperties := DefProperties<| hasCs1 := true |>;
            goodInstEncode := eq_refl;
            goodImmEncode := ltac:(eexists; cbv; eauto)
          |};
          {|instName := "SLLI";
            uniqId := [fieldVal opcodeField (5'b"00100");
                       fieldVal funct3Field (3'b"001");
                       if Xlen =? 32
                       then fieldVal funct7Field (7'b"0000000")
                       else fieldVal funct6Field (6'b"000000")];
            immEncoder := [ if Xlen =? 32
                            then Build_ImmEncoder (fst rs2FixedField) imm5
                            else Build_ImmEncoder (fst rs2FixedField) imm6 ];
            spec ty pc inst cs1 cs2 scr csr :=
              ( RetE ((DefWbFullOutput ty)
                        @%[ "cdVal" <- ((cs1 @% "val") <<
                                          (ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm inst)))]));
            instProperties := DefProperties<| hasCs1 := true |>;
            goodInstEncode := _;
            goodImmEncode := _
          |};
          {|instName := "SRLI";
            uniqId := [fieldVal opcodeField (5'b"00100");
                       fieldVal funct3Field (3'b"101");
                       if Xlen =? 32
                       then fieldVal funct7Field (7'b"0000000")
                       else fieldVal funct6Field (6'b"000000")];
            immEncoder := [ if Xlen =? 32
                            then Build_ImmEncoder (fst rs2FixedField) imm5
                            else Build_ImmEncoder (fst rs2FixedField) imm6 ];
            spec ty pc inst cs1 cs2 scr csr :=
              ( RetE ((DefWbFullOutput ty)
                        @%[ "cdVal" <- UniBit (TruncLsb Xlen 1)
                                         ((ZeroExtend 1 (cs1 @% "val")) >>>
                                            (ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm inst)))]));
            instProperties := DefProperties<| hasCs1 := true |>;
            goodInstEncode := _;
            goodImmEncode := _
          |};
          {|instName := "SRAI";
            uniqId := [fieldVal opcodeField (5'b"00100");
                       fieldVal funct3Field (3'b"101");
                       if Xlen =? 32
                       then fieldVal funct7Field (7'b"0100000")
                       else fieldVal funct6Field (6'b"010000")];
            immEncoder := [ if Xlen =? 32
                            then Build_ImmEncoder (fst rs2FixedField) imm5
                            else Build_ImmEncoder (fst rs2FixedField) imm6 ];
            spec ty pc inst cs1 cs2 scr csr :=
              ( RetE ((DefWbFullOutput ty)
                        @%[ "cdVal" <- UniBit (TruncLsb Xlen 1)
                                         ((SignExtend 1 (cs1 @% "val")) >>>
                                            (ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm inst)))]));
            instProperties := DefProperties<| hasCs1 := true |>;
            goodInstEncode := _;
            goodImmEncode := _
          |};
          {|instName := "Add";
            uniqId := [fieldVal opcodeField (5'b"01100");
                       fieldVal funct3Field (3'b"000");
                       fieldVal funct7Field (7'b"0000000")];
            immEncoder := [];
            spec ty pc inst cs1 cs2 scr csr :=
              ( RetE ((DefWbFullOutput ty)
                        @%[ "cdVal" <- (cs1 @% "val") + (cs2 @% "val")]));
            instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>;
            goodInstEncode := eq_refl;
            goodImmEncode := ltac:(eexists; cbv; eauto)
          |};
          {|instName := "Sub";
            uniqId := [fieldVal opcodeField (5'b"01100");
                       fieldVal funct3Field (3'b"000");
                       fieldVal funct7Field (7'b"0100000")];
            immEncoder := [];
            spec ty pc inst cs1 cs2 scr csr :=
              ( RetE ((DefWbFullOutput ty)
                        @%[ "cdVal" <- (cs1 @% "val") - (cs2 @% "val")]));
            instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>;
            goodInstEncode := eq_refl;
            goodImmEncode := ltac:(eexists; cbv; eauto)
          |};
          {|instName := "SLT";
            uniqId := [fieldVal opcodeField (5'b"01100");
                       fieldVal funct3Field (3'b"010");
                       fieldVal funct7Field (7'b"0000000")];
            immEncoder := [];
            spec ty pc inst cs1 cs2 scr csr :=
              ( LETC in1 <- SignExtend 1 (cs1 @% "val");
                LETC in2 <- SignExtend 1 (cs2 @% "val");
                LETC res <- UniBit (TruncMsb Xlen 1) (#in1 - #in2);
                RetE ((DefWbFullOutput ty)
                        @%[ "cdVal" <- ZeroExtendTruncLsb Xlen #res]));
            instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>;
            goodInstEncode := eq_refl;
            goodImmEncode := ltac:(eexists; cbv; eauto)
          |};
          {|instName := "SLTU";
            uniqId := [fieldVal opcodeField (5'b"01100");
                       fieldVal funct3Field (3'b"011");
                       fieldVal funct7Field (7'b"0000000")];
            immEncoder := [];
            spec ty pc inst cs1 cs2 scr csr :=
              ( LETC in1 <- ZeroExtend 1 (cs1 @% "val");
                LETC in2 <- ZeroExtend 1 (cs2 @% "val");
                LETC res <- UniBit (TruncMsb Xlen 1) (#in1 - #in2);
                RetE ((DefWbFullOutput ty)
                        @%[ "cdVal" <- ZeroExtendTruncLsb Xlen #res]));
            instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>;
            goodInstEncode := eq_refl;
            goodImmEncode := ltac:(eexists; cbv; eauto)
          |};
          {|instName := "Xor";
            uniqId := [fieldVal opcodeField (5'b"01100");
                       fieldVal funct3Field (3'b"100");
                       fieldVal funct7Field (7'b"0000000")];
            immEncoder := [];
            spec ty pc inst cs1 cs2 scr csr :=
              ( RetE ((DefWbFullOutput ty)
                        @%[ "cdVal" <- (cs1 @% "val") .^ (cs2 @% "val")]));
            instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>;
            goodInstEncode := eq_refl;
            goodImmEncode := ltac:(eexists; cbv; eauto)
          |};
          {|instName := "Or";
            uniqId := [fieldVal opcodeField (5'b"01100");
                       fieldVal funct3Field (3'b"110");
                       fieldVal funct7Field (7'b"0000000")];
            immEncoder := [];
            spec ty pc inst cs1 cs2 scr csr :=
              ( RetE ((DefWbFullOutput ty)
                        @%[ "cdVal" <- (cs1 @% "val") .| (cs2 @% "val")]));
            instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>;
            goodInstEncode := eq_refl;
            goodImmEncode := ltac:(eexists; cbv; eauto)
          |};
          {|instName := "And";
            uniqId := [fieldVal opcodeField (5'b"01100");
                       fieldVal funct3Field (3'b"111");
                       fieldVal funct7Field (7'b"0000000")];
            immEncoder := [];
            spec ty pc inst cs1 cs2 scr csr :=
              ( RetE ((DefWbFullOutput ty)
                        @%[ "cdVal" <- (cs1 @% "val") .& (cs2 @% "val")]));
            instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>;
            goodInstEncode := eq_refl;
            goodImmEncode := ltac:(eexists; cbv; eauto)
          |};
          {|instName := "SLL";
            uniqId := [fieldVal opcodeField (5'b"01100");
                       fieldVal funct3Field (3'b"001");
                       fieldVal funct7Field (7'b"0000000")];
            immEncoder := [];
            spec ty pc inst cs1 cs2 scr csr :=
              ( RetE ((DefWbFullOutput ty)
                        @%[ "cdVal" <- (cs1 @% "val") <<
                                         (ZeroExtendTruncLsb (Nat.log2_up Xlen) (cs2 @% "val"))]));
            instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>;
            goodInstEncode := eq_refl;
            goodImmEncode := ltac:(eexists; cbv; eauto)
          |};
          {|instName := "SRL";
            uniqId := [fieldVal opcodeField (5'b"01100");
                       fieldVal funct3Field (3'b"101");
                       fieldVal funct7Field (7'b"0000000")];
            immEncoder := [];
            spec ty pc inst cs1 cs2 scr csr :=
              ( RetE ((DefWbFullOutput ty)
                        @%[ "cdVal" <- UniBit (TruncLsb Xlen 1)
                                         ((ZeroExtend 1 (cs1 @% "val")) >>>
                                            (ZeroExtendTruncLsb (Nat.log2_up Xlen) (cs2 @% "val")))]));
            instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>;
            goodInstEncode := eq_refl;
            goodImmEncode := ltac:(eexists; cbv; eauto)
          |};
          {|instName := "SRA";
            uniqId := [fieldVal opcodeField (5'b"01100");
                       fieldVal funct3Field (3'b"101");
                       fieldVal funct7Field (7'b"0100000")];
            immEncoder := [];
            spec ty pc inst cs1 cs2 scr csr :=
              ( RetE ((DefWbFullOutput ty)
                        @%[ "cdVal" <- UniBit (TruncLsb Xlen 1)
                                         ((SignExtend 1 (cs1 @% "val")) >>>
                                            (ZeroExtendTruncLsb (Nat.log2_up Xlen) (cs2 @% "val")))]));
            instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>;
            goodInstEncode := eq_refl;
            goodImmEncode := ltac:(eexists; cbv; eauto)
          |}
        ]
      |}; destruct (Xlen =? 32); (reflexivity || eexists; cbv; eauto).
  Defined.
  
  Definition alu64Insts: InstEntryFull FullOutput :=
    {|xlens := [64];
      extension := Base;
      instEntries := [
        {|instName := "AddIW";
          uniqId := [fieldVal opcodeField (5'b"00110");
                     fieldVal funct3Field (3'b"000")];
          immEncoder := [Build_ImmEncoder (fst immField) imm12 ];
          spec ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefWbFullOutput ty)
                      @%[ "cdVal" <- Trunc32Signed Xlen ((cs1 @% "val") + SignExtendTruncLsb Xlen (imm inst))]));
          instProperties := DefProperties<| hasCs1 := true |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |};
        {|instName := "SLLIW";
          uniqId := [fieldVal opcodeField (5'b"00110");
                     fieldVal funct3Field (3'b"001");
                     fieldVal funct7Field (7'b"0000000")];
          immEncoder := [Build_ImmEncoder (fst rs2FixedField) imm5 ];
          spec ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefWbFullOutput ty)
                      @%[ "cdVal" <- Trunc32Signed Xlen ((cs1 @% "val") <<
                                                           (ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm inst)))]));
          instProperties := DefProperties<| hasCs1 := true |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |};
        {|instName := "SRLIW";
          uniqId := [fieldVal opcodeField (5'b"00110");
                     fieldVal funct3Field (3'b"101");
                     fieldVal funct7Field (7'b"0000000")];
          immEncoder := [Build_ImmEncoder (fst rs2FixedField) imm5 ];
          spec ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefWbFullOutput ty)
                      @%[ "cdVal" <- (Trunc32Unsigned Xlen (cs1 @% "val")) >>>
                                       (ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm inst))]));
          instProperties := DefProperties<| hasCs1 := true |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |};
        {|instName := "SRAIW";
          uniqId := [fieldVal opcodeField (5'b"00110");
                     fieldVal funct3Field (3'b"101");
                     fieldVal funct7Field (7'b"0100000")];
          immEncoder := [Build_ImmEncoder (fst rs2FixedField) imm5 ];
          spec ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefWbFullOutput ty)
                      @%[ "cdVal" <- (Trunc32Signed Xlen (cs1 @% "val")) >>>
                                       (ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm inst))]));
          instProperties := DefProperties<| hasCs1 := true |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |};
        {|instName := "AddW";
          uniqId := [fieldVal opcodeField (5'b"01110");
                     fieldVal funct3Field (3'b"000");
                     fieldVal funct7Field (7'b"0000000")];
          immEncoder := [];
          spec ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefWbFullOutput ty)
                      @%[ "cdVal" <- Trunc32Signed Xlen ((cs1 @% "val") + (cs2 @% "val"))]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |};
        {|instName := "SubW";
          uniqId := [fieldVal opcodeField (5'b"01110");
                     fieldVal funct3Field (3'b"000");
                     fieldVal funct7Field (7'b"0100000")];
          immEncoder := [];
          spec ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefWbFullOutput ty)
                      @%[ "cdVal" <- Trunc32Signed Xlen ((cs1 @% "val") - (cs2 @% "val"))]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |};
        {|instName := "SLLW";
          uniqId := [fieldVal opcodeField (5'b"01110");
                     fieldVal funct3Field (3'b"001");
                     fieldVal funct7Field (7'b"0000000")];
          immEncoder := [];
          spec ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefWbFullOutput ty)
                      @%[ "cdVal" <- Trunc32Signed Xlen
                                       ((cs1 @% "val") <<
                                          (ZeroExtendTruncLsb (Nat.log2_up Xlen) (cs2 @% "val")))]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |};
        {|instName := "SRLW";
          uniqId := [fieldVal opcodeField (5'b"01110");
                     fieldVal funct3Field (3'b"101");
                     fieldVal funct7Field (7'b"0000000")];
          immEncoder := [];
          spec ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefWbFullOutput ty)
                      @%[ "cdVal" <- (Trunc32Unsigned Xlen (cs1 @% "val")) >>>
                                       (ZeroExtendTruncLsb (Nat.log2_up Xlen) (cs2 @% "val"))]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |};
        {|instName := "SRAW";
          uniqId := [fieldVal opcodeField (5'b"01110");
                     fieldVal funct3Field (3'b"101");
                     fieldVal funct7Field (7'b"0100000")];
          immEncoder := [];
          spec ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefWbFullOutput ty)
                      @%[ "cdVal" <- (Trunc32Signed Xlen (cs1 @% "val")) >>>
                                       (ZeroExtendTruncLsb (Nat.log2_up Xlen) (cs2 @% "val"))]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |}
      ]
    |}.

  Definition justFullCap ty (x: FullCapWithTag @# ty) : FullCap @# ty :=
    STRUCT { "cap" ::= x @% "cap";
             "val" ::= x @% "val" }.
        

  Definition representableFn ty (cs1: FullCap @# ty) (addr: Addr @# ty) : Bool ## ty :=
    ( LETE baseTop <- getCapBaseTop capAccessors (cs1 @% "cap") (cs1 @% "val");
      LETE baseTop2 <- getCapBaseTop capAccessors (cs1 @% "cap") addr;
      RetE ((#baseTop @% "aTopBase") == (#baseTop2 @% "aTopBase")) ).

  Definition setBounds ty (cs1: FullCapWithTag @# ty) (len: Data @# ty) (isExact: Bool @# ty): FullCapWithTag ## ty :=
    ( LETE baseTop <- getCapBaseTop capAccessors (cs1 @% "cap") (cs1 @% "val");
      LETC baseBound <- (cs1 @% "val") >= (#baseTop @% "base");
      LETC topBound <- (ZeroExtend 1 (cs1 @% "val") + ZeroExtend 1 len) <= (#baseTop @% "top");
      LETE capBounds <- getCapBounds capAccessors (cs1 @% "val") len;
      LETC newCap <- setCapBounds capAccessors
                       (cs1 @% "cap") (#capBounds @% "B") (#capBounds @% "T") (#capBounds @% "exp");
      RetE (STRUCT {
                "tag" ::= (cs1 @% "tag") && !isSealed capAccessors (cs1 @% "cap") && (#baseBound && #topBound)
                          && (!isExact || (#capBounds @% "exact?"));
                "cap" ::= #newCap;
                "val" ::= cs1 @% "val" } : FullCapWithTag @# ty) ).

  Definition CgpIndex := 3.
  
  Definition capInsts: InstEntryFull FullOutput :=
    {|xlens := [32; 64];
      extension := Base;
      instEntries := [
        {|instName := "AUICGP";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"7b"))];
          immEncoder := [Build_ImmEncoder (fst auiLuiField) imm20_U];
          spec ty pc inst cs1 cs2 scr csr :=
            ( LETC newAddr <- (cs1 @% "val") + SignExtendTruncLsb Xlen ({< auiLuiOffset inst, $$(wzero 11) >});
              LETE representable <- representableFn (justFullCap cs1) #newAddr;
              RetE ((DefWbFullOutput ty)
                      @%[ "cdTag" <- (cs1 @% "tag") && !isSealed capAccessors (cs1 @% "cap") && #representable ]
                      @%[ "cdCap" <- cs1 @% "cap" ]
                      @%[ "cdVal" <- #newAddr ]));
          instProperties := DefProperties<| implicitReg := CgpIndex |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |};
        {|instName := "AUIPCC";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"17"))];
          immEncoder := [Build_ImmEncoder (fst auiLuiField) imm20_U];
          spec ty pc inst cs1 cs2 scr csr :=
            ( LETC newAddr <- (pc @% "val") + SignExtendTruncLsb Xlen ({< auiLuiOffset inst, $$(wzero 11) >});
              LETE representable <- representableFn pc #newAddr;
              RetE ((DefWbFullOutput ty)
                      @%[ "cdTag" <- #representable ]
                      @%[ "cdCap" <- pc @% "cap" ]
                      @%[ "cdVal" <- #newAddr ]));
          instProperties := DefProperties;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |};
        {|instName := "CAndPerm";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal funct7Field (7'h"d")];
          immEncoder := [];
          spec ty pc inst cs1 cs2 scr csr :=
            ( LETE perms <- getCapPerms capAccessors (cs1 @% "cap");
              LETC newPerms <- unpack CapPerms (ZeroExtendTruncLsb (size CapPerms)
                                                  ((ZeroExtendTruncLsb Xlen (pack #perms)) .& (cs2 @% "val")));
              LETE newCap <- setCapPerms capAccessors #newPerms (cs1 @% "cap");
              RetE ((DefWbFullOutput ty)
                      @%[ "cdTag" <- cs1 @% "tag" ]
                      @%[ "cdCap" <- #newCap ]
                      @%[ "cdVal" <- cs1 @% "val" ]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |};
        {|instName := "CClearTag";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal rs2FixedField (5'h"b");
                     fieldVal funct7Field (7'h"7f")];
          immEncoder := [];
          spec ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefWbFullOutput ty)
                      @%[ "cdTag" <- $$false ]
                      @%[ "cdCap" <- cs1 @% "cap" ]
                      @%[ "cdVal" <- cs1 @% "val" ]));
          instProperties := DefProperties<| hasCs1 := true |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |};
        {|instName := "CGetAddr";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal rs2FixedField (5'h"f");
                     fieldVal funct7Field (7'h"7f")];
          immEncoder := [];
          spec ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefWbFullOutput ty)
                      @%[ "cdVal" <- cs1 @% "val" ]));
          instProperties := DefProperties<| hasCs1 := true |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |};
        {|instName := "CGetBase";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal rs2FixedField (5'h"2");
                     fieldVal funct7Field (7'h"7f")];
          immEncoder := [];
          spec ty pc inst cs1 cs2 scr csr :=
            ( LETE baseTop <- getCapBaseTop capAccessors (cs1 @% "cap") (cs1 @% "val");
              RetE ((DefWbFullOutput ty)
                      @%[ "cdVal" <- #baseTop @% "base" ]));
          instProperties := DefProperties<| hasCs1 := true |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |};
        {|instName := "CGetHigh";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal rs2FixedField (5'h"17");
                     fieldVal funct7Field (7'h"7f")];
          immEncoder := [];
          spec ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefWbFullOutput ty)
                      @%[ "cdVal" <- cs1 @% "cap" ]));
          instProperties := DefProperties<| hasCs1 := true |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |};
        {|instName := "CGetLen";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal rs2FixedField (5'h"3");
                     fieldVal funct7Field (7'h"7f")];
          immEncoder := [];
          spec ty pc inst cs1 cs2 scr csr :=
            ( LETE baseTop <- getCapBaseTop capAccessors (cs1 @% "cap") (cs1 @% "val");
              LETC len <- (#baseTop @% "top") - (ZeroExtend 1 (#baseTop @% "base"));
              LETC lenMsb <- unpack Bool (UniBit (TruncMsb Xlen 1) #len);
              LETC lenLsb <- UniBit (TruncLsb Xlen 1) #len;
              RetE ((DefWbFullOutput ty)
                      @%[ "cdVal" <- ITE #lenMsb $$(wones Xlen) #lenLsb ]));
          instProperties := DefProperties<| hasCs1 := true |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |};
        {|instName := "CGetPerm";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal rs2FixedField (5'h"0");
                     fieldVal funct7Field (7'h"7f")];
          immEncoder := [];
          spec ty pc inst cs1 cs2 scr csr :=
            ( LETE perms <- getCapPerms capAccessors (cs1 @% "cap");
              RetE ((DefWbFullOutput ty)
                      @%[ "cdVal" <- ZeroExtendTruncLsb Xlen (pack #perms) ]));
          instProperties := DefProperties<| hasCs1 := true |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |};
        {|instName := "CGetTag";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal rs2FixedField (5'h"4");
                     fieldVal funct7Field (7'h"7f")];
          immEncoder := [];
          spec ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefWbFullOutput ty)
                      @%[ "cdVal" <- ZeroExtendTruncLsb Xlen (pack (cs1 @% "tag")) ]));
          instProperties := DefProperties<| hasCs1 := true |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |};
        {|instName := "CGetTop";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal rs2FixedField (5'h"18");
                     fieldVal funct7Field (7'h"7f")];
          immEncoder := [];
          spec ty pc inst cs1 cs2 scr csr :=
            ( LETE baseTop <- getCapBaseTop capAccessors (cs1 @% "cap") (cs1 @% "val");
              LETC topMsb <- unpack Bool (UniBit (TruncMsb Xlen 1) (#baseTop @% "top"));
              LETC topLsb <- UniBit (TruncLsb Xlen 1) (#baseTop @% "top");
              RetE ((DefWbFullOutput ty)
                      @%[ "cdVal" <- ITE #topMsb $$(wones Xlen) #topLsb ]));
          instProperties := DefProperties<| hasCs1 := true |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |};
        {|instName := "CGetType";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal rs2FixedField (5'h"1");
                     fieldVal funct7Field (7'h"7f")];
          immEncoder := [];
          spec ty pc inst cs1 cs2 scr csr :=
            ( LETC oType <- getCapOType capAccessors (cs1 @% "cap");
              RetE ((DefWbFullOutput ty)
                      @%[ "cdVal" <- ZeroExtendTruncLsb Xlen #oType ]));
          instProperties := DefProperties<| hasCs1 := true |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |};
        {|instName := "CIncAddr";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal funct7Field (7'h"11")];
          immEncoder := [];
          spec ty pc inst cs1 cs2 scr csr :=
            ( LETC newAddr <- (cs1 @% "val") + (cs2 @% "val");
              LETE representable <- representableFn (justFullCap cs1) #newAddr;
              RetE ((DefWbFullOutput ty)
                      @%[ "cdTag" <- (cs1 @% "tag") && !isSealed capAccessors (cs1 @% "val") && #representable ]
                      @%[ "cdCap" <- cs1 @% "cap" ]
                      @%[ "cdVal" <- #newAddr ]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |};
        {|instName := "CIncAddrImm";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"1")];
          immEncoder := [Build_ImmEncoder (fst immField) imm12];
          spec ty pc inst cs1 cs2 scr csr :=
            ( LETC newAddr <- (cs1 @% "val") + SignExtendTruncLsb Xlen (imm inst);
              LETE representable <- representableFn (justFullCap cs1) #newAddr;
              RetE ((DefWbFullOutput ty)
                      @%[ "cdTag" <- (cs1 @% "tag") && !isSealed capAccessors (cs1 @% "val") && #representable ]
                      @%[ "cdCap" <- cs1 @% "cap" ]
                      @%[ "cdVal" <- #newAddr ]));
          instProperties := DefProperties<| hasCs1 := true |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |};
        {|instName := "CMove";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal rs2FixedField (5'h"a");
                     fieldVal funct7Field (7'h"7f")];
          immEncoder := [];
          spec ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefWbFullOutput ty)
                      @%[ "cdTag" <- cs1 @% "tag" ]
                      @%[ "cdCap" <- cs1 @% "cap" ]
                      @%[ "cdVal" <- cs1 @% "val" ]));
          instProperties := DefProperties<| hasCs1 := true |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |};
        {|instName := "CRepresentableAlignmentMask";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal rs2FixedField (5'h"9");
                     fieldVal funct7Field (7'h"7f")];
          immEncoder := [];
          spec ty pc inst cs1 cs2 scr csr :=
            ( LETE capBounds <- getCapBounds capAccessors ($0) (cs1 @% "val");
              LETC mask <- $$(wones Xlen) << (#capBounds @% "exp");
              RetE ((DefWbFullOutput ty)
                      @%[ "cdVal" <- #mask ]));
          instProperties := DefProperties<| hasCs1 := true |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |};
        {|instName := "CRoundRepresentableLength";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal rs2FixedField (5'h"8");
                     fieldVal funct7Field (7'h"7f")];
          immEncoder := [];
          spec ty pc inst cs1 cs2 scr csr :=
            ( LETE capBounds <- getCapBounds capAccessors ($0) (cs1 @% "val");
              LETC mask <- $$(wones Xlen) << (#capBounds @% "exp");
              LETC repLen <- (cs1 @% "val" + (~#mask)) .& #mask;
              RetE ((DefWbFullOutput ty)
                      @%[ "cdVal" <- #repLen ]));
          instProperties := DefProperties<| hasCs1 := true |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |};
        {|instName := "CSetAddr";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal funct7Field (7'h"10")];
          immEncoder := [];
          spec ty pc inst cs1 cs2 scr csr :=
            ( LETC newAddr <- cs2 @% "val";
              LETE representable <- representableFn (justFullCap cs1) #newAddr;
              RetE ((DefWbFullOutput ty)
                      @%[ "cdTag" <- (cs1 @% "tag") && !isSealed capAccessors (cs1 @% "val") && #representable ]
                      @%[ "cdCap" <- cs1 @% "cap" ]
                      @%[ "cdVal" <- #newAddr ]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |};
        {|instName := "CSetBounds";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal funct7Field (7'h"8")];
          immEncoder := [];
          spec ty pc inst cs1 cs2 scr csr :=
            ( LETE newCd <- setBounds cs1 (cs2 @% "val") $$false;
              RetE ((DefWbFullOutput ty)
                      @%[ "cdTag" <- #newCd @% "tag" ]
                      @%[ "cdCap" <- #newCd @% "cap" ]
                      @%[ "cdVal" <- #newCd @% "val" ]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |};
        {|instName := "CSetBoundsExact";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal funct7Field (7'h"9")];
          immEncoder := [];
          spec ty pc inst cs1 cs2 scr csr :=
            ( LETE newCd <- setBounds cs1 (cs2 @% "val") $$true;
              RetE ((DefWbFullOutput ty)
                      @%[ "cdTag" <- #newCd @% "tag" ]
                      @%[ "cdCap" <- #newCd @% "cap" ]
                      @%[ "cdVal" <- #newCd @% "val" ]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |};
        {|instName := "CSetBoundsImm";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"2")];
          immEncoder := [Build_ImmEncoder (fst immField) imm12];
          spec ty pc inst cs1 cs2 scr csr :=
            ( LETE newCd <- setBounds cs1 (ZeroExtendTruncLsb Xlen (imm inst)) $$false;
              RetE ((DefWbFullOutput ty)
                      @%[ "cdTag" <- #newCd @% "tag" ]
                      @%[ "cdCap" <- #newCd @% "cap" ]
                      @%[ "cdVal" <- #newCd @% "val" ]));
          instProperties := DefProperties<| hasCs1 := true |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |};
        {|instName := "CSetEqualExact";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal funct7Field (7'h"21")];
          immEncoder := [];
          spec ty pc inst cs1 cs2 scr csr :=
            ( LETC tagEq <- (cs1 @% "tag") == (cs2 @% "tag");
              LETC capEq <- (cs1 @% "cap") == (cs2 @% "cap");
              LETC valEq <- (cs1 @% "val") == (cs2 @% "val");
              RetE ((DefWbFullOutput ty)
                      @%[ "cdVal" <- ZeroExtendTruncLsb Xlen (pack (#tagEq && #capEq && #valEq)) ]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |};
        {|instName := "CSetHigh";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal funct7Field (7'h"16")];
          immEncoder := [];
          spec ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefWbFullOutput ty)
                      @%[ "cdTag" <- $$false ]
                      @%[ "cdCap" <- cs2 @% "val" ]
                      @%[ "cdVal" <- cs1 @% "val" ]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |};
        {|instName := "CSub";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal funct7Field (7'h"14")];
          immEncoder := [];
          spec ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefWbFullOutput ty)
                      @%[ "cdVal" <- (cs1 @% "val") - (cs2 @% "val") ]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |};
        {|instName := "CTestSubset";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal funct7Field (7'h"20")];
          immEncoder := [];
          spec ty pc inst cs1 cs2 scr csr :=
            ( LETE baseTop <- getCapBaseTop capAccessors (cs1 @% "cap") (cs1 @% "val");
              LETE baseTop2 <- getCapBaseTop capAccessors (cs2 @% "cap") (cs2 @% "val");
              LETC baseBound <- (#baseTop2 @% "base") >= (#baseTop @% "base");
              LETC topBound <- (#baseTop2 @% "top") <= (#baseTop @% "top");
              LETC tagEq <- (cs1 @% "tag") == (cs2 @% "tag");
              LETE perms <- getCapPerms capAccessors (cs1 @% "cap");
              LETE perms2 <- getCapPerms capAccessors (cs2 @% "cap");
              LETC permsAnd <- (pack #perms .& pack #perms2);
              LETC permsSub <- #permsAnd == pack #perms2;
              RetE ((DefWbFullOutput ty)
                      @%[ "cdVal" <-
                            ZeroExtendTruncLsb Xlen (pack (#baseBound && #topBound && #tagEq && #permsSub)) ]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |};
        {|instName := "CSeal";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal funct7Field (7'h"b")];
          immEncoder := [];
          spec ty pc inst cs1 cs2 scr csr :=
            ( LETE baseTop2 <- getCapBaseTop capAccessors (cs2 @% "cap") (cs2 @% "val");
              LETC baseBound <- (cs2 @% "val") >= (#baseTop2 @% "base");
              LETC topBound <- ZeroExtend 1 (cs2 @% "val") + $1 <= (#baseTop2 @% "top");
              LETE perms <- getCapPerms capAccessors (cs1 @% "cap");
              LETE perms2 <- getCapPerms capAccessors (cs2 @% "cap");
              LETC validSealAddr <- isSealAddr capAccessors (cs2 @% "val") (#perms @% "EX");
              LETC newCap <- seal capAccessors
                               (ZeroExtendTruncLsb (CapOTypeSz capAccessors) (cs2 @% "val")) (cs1 @% "cap");
              RetE ((DefWbFullOutput ty)
                      @%[ "cdTag" <- (cs2 @% "tag") && !isSealed capAccessors (cs2 @% "cap") &&
                                       (#baseBound && #topBound) && (cs1 @% "tag") &&
                                       !isSealed capAccessors (cs1 @% "cap") && (#perms2 @% "SE") && #validSealAddr]
                      @%[ "cdCap" <- #newCap ]
                      @%[ "cdVal" <- cs1 @% "val" ]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |};
        {|instName := "CUnseal";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal funct7Field (7'h"c")];
          immEncoder := [];
          spec ty pc inst cs1 cs2 scr csr :=
            ( LETE baseTop2 <- getCapBaseTop capAccessors (cs2 @% "cap") (cs2 @% "val");
              LETC baseBound <- (cs2 @% "val") >= (#baseTop2 @% "base");
              LETC topBound <- ZeroExtend 1 (cs2 @% "val") + $1 <= (#baseTop2 @% "top");
              LETC oType <- getCapOType capAccessors (cs1 @% "cap");
              LETC oTypeEq <- ZeroExtendTruncLsb Xlen #oType == (cs2 @% "val");
              LETE perms <- getCapPerms capAccessors (cs1 @% "cap");
              LETE perms2 <- getCapPerms capAccessors (cs2 @% "cap");
              LETC newPerms <- #perms @%[ "GL" <- #perms @% "GL" && #perms2 @% "GL" ];
              LETE newCapWithPerms <- setCapPerms capAccessors #newPerms (cs1 @% "cap");
              LETC newCap <- unseal capAccessors #newCapWithPerms;
              RetE ((DefWbFullOutput ty)
                      @%[ "cdTag" <- (cs2 @% "tag") && !isSealed capAccessors (cs2 @% "cap") &&
                                       (#baseBound && #topBound) && (cs1 @% "tag") &&
                                       isSealed capAccessors (cs1 @% "cap") && (#perms2 @% "US") && #oTypeEq]
                      @%[ "cdCap" <- #newCap ]
                      @%[ "cdVal" <- cs1 @% "val" ]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |}
      ]
    |}.

  Definition mkBranchInst (name: string) funct3Val (takenFn: forall {ty}, Data @# ty -> Data @# ty -> Bool ## ty) :=
      {|instName := name;
        uniqId := [fieldVal opcodeField (5'b"11000");
                   fieldVal funct3Field funct3Val];
        immEncoder := [Build_ImmEncoder (fst rdFixedField) imm5_B;
                       Build_ImmEncoder (fst funct7Field) imm7_B];
        spec ty pc inst cs1 cs2 scr csr :=
          ( LETC newAddr <- (pc @% "val") + SignExtendTruncLsb Xlen (branchOffset inst);
            LETE taken <- takenFn (cs1 @% "val") (cs2 @% "val");
            LETC size <- $(if compressed then 2 else 4);
            LETE baseTop <- getCapBaseTop capAccessors (pc @% "cap") (pc @% "val");
            LETC baseBound <- #newAddr >= (#baseTop @% "base");
            LETC topBound <- ZeroExtend 1 #newAddr + #size <= (#baseTop @% "top");
            LETC inBounds <- #baseBound && #topBound;
            RetE ((DefFullOutput ty)
                    @%[ "taken?" <- #taken ]
                    @%[ "pcMemAddr" <- #newAddr ]
                    @%[ "exception?" <- if compressed
                                        then !#inBounds
                                        else !#inBounds || isNotZero (ZeroExtendTruncLsb 2 #newAddr) ]
                    @%[ "exceptionCause" <- if compressed
                                            then Const ty (natToWord Xlen CapBoundsViolation)
                                            else (IF #inBounds
                                                  then Const ty (natToWord Xlen InstMisaligned)
                                                  else Const ty (natToWord Xlen CapBoundsViolation))]
                    @%[ "exceptionValue" <- #newAddr ]
                    @%[ "baseException?" <- #inBounds ]
                    @%[ "pcCapException?" <- !#inBounds ]));
        instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |><| hasCd := false |>;
        goodInstEncode := eq_refl;
        goodImmEncode := ltac:(eexists; cbv; eauto)
      |}.

  Definition branchInsts: InstEntryFull FullOutput :=
    {|xlens := [32; 64];
      extension := Base;
      instEntries := [
        mkBranchInst "BEq" ('b"000") (fun ty rs1 rs2 => RetE (rs1 == rs2));
        mkBranchInst "BNE" ('b"001") (fun ty rs1 rs2 => RetE !(rs1 == rs2));
        mkBranchInst "BLT" ('b"100") (fun ty rs1 rs2 =>
                                        ( LETC a <- SignExtend 1 rs1;
                                          LETC b <- SignExtend 1 rs2;
                                          LETC res <- #a - #b;
                                          RetE (unpack Bool (UniBit (TruncMsb Xlen 1) #res))));
        mkBranchInst "BGE" ('b"101") (fun ty rs1 rs2 =>
                                        ( LETC a <- SignExtend 1 rs1;
                                          LETC b <- SignExtend 1 rs2;
                                          LETC res <- #a - #b;
                                          RetE !(unpack Bool (UniBit (TruncMsb Xlen 1) #res))));
        mkBranchInst "BLTU" ('b"110") (fun ty rs1 rs2 =>
                                         ( LETC a <- ZeroExtend 1 rs1;
                                           LETC b <- ZeroExtend 1 rs2;
                                           LETC res <- #a - #b;
                                           RetE (unpack Bool (UniBit (TruncMsb Xlen 1) #res))));
        mkBranchInst "BGEU" ('b"111") (fun ty rs1 rs2 =>
                                         ( LETC a <- ZeroExtend 1 rs1;
                                           LETC b <- ZeroExtend 1 rs2;
                                           LETC res <- #a - #b;
                                           RetE !(unpack Bool (UniBit (TruncMsb Xlen 1) #res))))
      ]
    |}.

  Definition isBranchInsts ty (inst: Inst @# ty) :=
    redLet (@Kor _ _) (fun x => RetE (matchUniqId inst (uniqId x))) (filterInsts [branchInsts]).

  Definition mkLdInst (name: string) funct3Val (size: nat) (isCap sign: bool) :=
    {|instName := name;
      uniqId := [fieldVal opcodeField (5'b"00000");
                 fieldVal funct3Field funct3Val];
      immEncoder := [Build_ImmEncoder (fst immField) imm12];
      spec ty pc inst cs1 cs2 scr csr :=
        ( LETC newAddr <- (cs1 @% "val") + SignExtendTruncLsb Xlen (imm inst);
          LETE baseTop <- getCapBaseTop capAccessors (cs1 @% "cap") (cs1 @% "val");
          LETC baseBound <- #newAddr >= (#baseTop @% "base");
          LETC topBound <- ZeroExtend 1 #newAddr + $size <= (#baseTop @% "top");
          LETE perms <- getCapPerms capAccessors (cs1 @% "cap");
          LETC fullException
            : Maybe Data <-
                (IF !(cs1 @% "tag")
                 then Valid (Const ty (natToWord Xlen CapTagViolation))
                 else (IF isSealed capAccessors (cs1 @% "cap")
                       then Valid (Const ty (natToWord Xlen CapSealViolation))
                       else (IF !(#perms @% "LD")
                             then Valid (Const ty (natToWord Xlen CapLdViolation))
                             else (IF !(#baseBound && #topBound)
                                   then Valid (Const ty (natToWord Xlen CapBoundsViolation))
                                   else StaticIf isCap
                                          (isNotZero (ZeroExtendTruncLsb (Nat.log2_up ((Xlen + CapSz)/8)) #newAddr))
                                          (Valid (Const ty (natToWord Xlen CapLdMisaligned)))
                                          Invalid))));
          RetE ((DefWbFullOutput ty)
                  @%[ "exception?" <- #fullException @% "valid" ]
                  @%[ "exceptionCause" <- #fullException @% "data" ]
                  @%[ "pcMemAddr" <- #newAddr ]
                  @%[ "memCap?" <- $$isCap ]
                  @%[ "memSize" <- Const ty (natToWord MemSizeSz size) ]
                  @%[ "mem?" <- $$true ]
                  @%[ "ldSigned?" <- $$sign ]
                  @%[ "ldPerms" <- #perms ]));
      instProperties := DefProperties<| hasCs1 := true |><| isLoad := true |>;
      goodInstEncode := eq_refl;
      goodImmEncode := ltac:(eexists; cbv; eauto)
    |}.

  Definition ldInsts: InstEntryFull FullOutput :=
    {|xlens := [32; 64];
      extension := Base;
      instEntries := [
        mkLdInst "CLB"  ('b"000") 1 false true;
        mkLdInst "CLH"  ('b"001") 2 false true;
        mkLdInst "CLW"  ('b"010") 4 false true;
        mkLdInst "CLBU" ('b"100") 1 false false;
        mkLdInst "CLHU" ('b"101") 2 false false
      ]
    |}.
  
  Definition ld32Insts: InstEntryFull FullOutput :=
    {|xlens := [32];
      extension := Base;
      instEntries := [
        mkLdInst "CLC"  ('b"011") 8 true  false
      ]
    |}.
  
  Definition ld64Insts: InstEntryFull FullOutput :=
    {|xlens := [64];
      extension := Base;
      instEntries := [
        mkLdInst "CLWU" ('b"110") 4 false false
      ]
    |}.

  Definition mkStInst (name: string) funct3Val (size: nat) (isCap: bool) :=
    {|instName := name;
      uniqId := [fieldVal opcodeField (5'b"01000");
                 fieldVal funct3Field funct3Val];
      immEncoder := [Build_ImmEncoder (fst rdFixedField) imm5;
                     Build_ImmEncoder (fst funct7Field) imm7];
      spec ty pc inst cs1 cs2 scr csr :=
        ( LETC newAddr <- (cs1 @% "val") + SignExtendTruncLsb Xlen ({< funct7 inst, rdFixed inst >});
          LETE baseTop <- getCapBaseTop capAccessors (cs1 @% "cap") (cs1 @% "val");
          LETC baseBound <- #newAddr >= (#baseTop @% "base");
          LETC topBound <- ZeroExtend 1 #newAddr + $size <= (#baseTop @% "top");
          LETE perms <- getCapPerms capAccessors (cs1 @% "cap");
          LETE perms2 <- getCapPerms capAccessors (cs2 @% "cap");
          LETC newTag <- (cs2 @% "tag") && ((#perms2 @% "GL") || (#perms @% "SL"));
          LETC fullException
            : Maybe Data <-
                (IF !(cs1 @% "tag")
                 then Valid (Const ty (natToWord Xlen CapTagViolation))
                 else (IF isSealed capAccessors (cs1 @% "cap")
                       then Valid (Const ty (natToWord Xlen CapSealViolation))
                       else (IF !(#perms @% "SD")
                             then Valid (Const ty (natToWord Xlen CapStViolation))
                             else (IF !(#perms @% "MC")
                                   then Valid (Const ty (natToWord Xlen CapStCapViolation))
                                   else (IF !(#baseBound && #topBound)
                                         then Valid (Const ty (natToWord Xlen CapBoundsViolation))
                                         else StaticIf isCap
                                                (isNotZero
                                                   (ZeroExtendTruncLsb (Nat.log2_up ((Xlen + CapSz)/8))#newAddr))
                                                (Valid (Const ty (natToWord Xlen CapStMisaligned)))
                                                Invalid)))));
          RetE ((DefFullOutput ty)
                  @%[ "exception?" <- #fullException @% "valid" ]
                  @%[ "exceptionCause" <- #fullException @% "data" ]
                  @%[ "pcMemAddr" <- #newAddr ]
                  @%[ "memCap?" <- $$isCap ]
                  @%[ "memSize" <- Const ty (natToWord MemSizeSz size) ]
                  @%[ "mem?" <- $$true ]
                  @%[ "store?" <- $$true ]
                  @%[ "cdTag" <- #newTag]
                  @%[ "cdCap" <- cs2 @% "cap"]
                  @%[ "cdVal" <- cs2 @% "val"] ));
      instProperties :=
        DefProperties<| hasCs1 := true |><| hasCs2 := true |><| hasCd := false |><| isStore := true |>;
      goodInstEncode := eq_refl;
      goodImmEncode := ltac:(eexists; cbv; eauto)
    |}.

  Definition stInsts: InstEntryFull FullOutput :=
    {|xlens := [32; 64];
      extension := Base;
      instEntries := [
        mkStInst "CSB"  ('b"000") 1 false;
        mkStInst "CSH"  ('b"001") 2 false;
        mkStInst "CSW"  ('b"010") 4 false
      ]
    |}.
  
  Definition st32Insts: InstEntryFull FullOutput :=
    {|xlens := [32];
      extension := Base;
      instEntries := [
        mkStInst "CSC"  ('b"011") 8 true
      ]
    |}.
  
  Definition st64Insts: InstEntryFull FullOutput :=
    {|xlens := [64];
      extension := Base;
      instEntries := [
      ]
    |}.

  Definition MStatusIndex := (snd immField) 'h"300".

  Definition jumpInsts: InstEntryFull FullOutput :=
    {|xlens := [32; 64];
      extension := Base;
      instEntries := [
        {|instName := "CJAL";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"6f"))];
          immEncoder := [Build_ImmEncoder (fst auiLuiField) imm20_J];
          spec ty pc inst cs1 cs2 scr csr :=
            ( LETC newAddr <- (pc @% "val") + SignExtendTruncLsb Xlen (jalOffset inst);
              LETC linkAddr <- (pc @% "val") + ITE (isInstNotCompressed inst) $4 $2;
              LETC mstatusArr <- unpack (Array (S (Xlen-1)) Bool) (castBits XlenSXlenMinus1 csr);
              LETC ie <- #mstatusArr ![ 3 ];
              LETC size <- $(if compressed then 2 else 4);
              LETE baseTop <- getCapBaseTop capAccessors (pc @% "cap") (pc @% "val");
              LETC baseBound <- #newAddr >= (#baseTop @% "base");
              LETC topBound <- ZeroExtend 1 #newAddr + #size <= (#baseTop @% "top");
              LETC inBounds <- #baseBound && #topBound;
              RetE ((DefWbFullOutput ty)
                      @%[ "cdTag" <- $$true ]
                      @%[ "cdCap" <- seal capAccessors (getOTypeFromIe capAccessors #ie) (pc @% "cap") ]
                      @%[ "cdVal" <- #linkAddr ]
                      @%[ "taken?" <- $$true ]
                      @%[ "pcMemAddr" <- #newAddr ]
                      @%[ "exception?" <- if compressed
                                          then !#inBounds
                                          else !#inBounds || isNotZero (ZeroExtendTruncLsb 2 #newAddr) ]
                      @%[ "exceptionCause" <- if compressed
                                              then Const ty (natToWord Xlen CapBoundsViolation)
                                              else (IF #inBounds
                                                    then Const ty (natToWord Xlen InstMisaligned)
                                                    else Const ty (natToWord Xlen CapBoundsViolation)) ]
                      @%[ "exceptionValue" <- #newAddr ]
                      @%[ "baseException?" <- #inBounds ]
                      @%[ "pcCapException?" <- !#inBounds] ));
          instProperties := DefProperties <| implicitCsr := MStatusIndex |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |};
        {|instName := "CJALR";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"67"));
                     fieldVal funct3Field (3'h"0")];
          immEncoder := [Build_ImmEncoder (fst immField) imm12];
          spec ty pc inst cs1 cs2 scr csr :=
            ( LETC newAddrTemp <- (cs1 @% "val") + SignExtendTruncLsb Xlen (imm inst);
              LETC newAddr <- ZeroExtendTruncLsb Xlen ({< ZeroExtendTruncMsb (Xlen - 1) #newAddrTemp, $$WO~0 >});
              LETC linkAddr <- (pc @% "val") + ITE (isInstNotCompressed inst) $4 $2;
              LETE perms <- getCapPerms capAccessors (cs1 @% "cap");
              LETC size <- $(if compressed then 2 else 4);
              LETE baseTop <- getCapBaseTop capAccessors (pc @% "cap") (pc @% "val");
              LETC baseBound <- #newAddr >= (#baseTop @% "base");
              LETC topBound <- ZeroExtend 1 #newAddr + #size <= (#baseTop @% "top");
              LETC inBounds <- #baseBound && #topBound;
              LETC fullException
                : Pair (Maybe Data) Bool <-
                    (IF !(cs1 @% "tag")
                     then mkPair (Valid (Const ty (natToWord Xlen CapTagViolation))) ($$false)
                     else (IF isSealed capAccessors (cs1 @% "cap") &&
                             (!isSentry capAccessors (cs1 @% "cap") || isNotZero (imm inst) )
                           then mkPair (Valid (Const ty (natToWord Xlen CapSealViolation))) ($$false)
                           else (IF !(#perms @% "EX")
                                 then mkPair (Valid (Const ty (natToWord Xlen CapExecViolation))) ($$false)
                                 else (IF !#inBounds
                                       then mkPair (Valid (Const ty (natToWord Xlen CapBoundsViolation))) ($$false)
                                       else StaticIf (negb compressed) (isNotZero (ZeroExtendTruncLsb 2 #newAddr))
                                              (mkPair (Valid (Const ty (natToWord Xlen InstMisaligned))) ($$true))
                                              (mkPair Invalid ($$false))))));
              LETC mstatusArr <- unpack (Array (S (Xlen-1)) Bool) (castBits XlenSXlenMinus1 csr);
              LETC ie <- #mstatusArr ![ 3 ];
              LETC ieSentry <- isIeSentry capAccessors (cs1 @% "cap");
              LETC idSentry <- isIdSentry capAccessors (cs1 @% "cap");
              RetE ((DefWbFullOutput ty)
                      @%[ "cdTag" <- $$true ]
                      @%[ "cdCap" <- seal capAccessors (getOTypeFromIe capAccessors #ie) (pc @% "cap") ]
                      @%[ "cdVal" <- #linkAddr ]
                      @%[ "taken?" <- $$true ]
                      @%[ "pcMemAddr" <- #newAddr ]
                      @%[ "changePcCap?" <- $$true ]
                      @%[ "pcCap" <- unseal capAccessors (cs1 @% "cap") ]
                      @%[ "exception?" <- #fullException @% "fst" @% "valid" ]
                      @%[ "exceptionCause" <- #fullException @% "fst" @% "data" ]
                      @%[ "exceptionValue" <- #newAddr ]
                      @%[ "baseException?" <- #fullException @% "snd" ]
                      @%[ "changeIe?" <- #ieSentry || #idSentry ]
                      @%[ "newIe" <- #ieSentry ] ));
          instProperties := DefProperties<| hasCs1 := true |><| implicitCsr := MStatusIndex |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |}
      ]
    |}.

  Definition isJumpInsts ty (inst: Inst @# ty) :=
    redLet (@Kor _ _) (fun x => RetE (matchUniqId inst (uniqId x))) (filterInsts [jumpInsts]).


  Definition MepccIndex := 31.

  Definition exceptionInsts: InstEntryFull FullOutput :=
    {|xlens := [32; 64];
      extension := Base;
      instEntries := [
        {|instName := "ECall";
          uniqId := [fieldVal opcodeField (5'b"11100");
                     fieldVal rdFixedField (5'h"0");
                     fieldVal funct3Field (3'h"0");
                     fieldVal rs1FixedField (5'h"0");
                     fieldVal rs2FixedField (5'h"0");
                     fieldVal funct7Field (7'h"0")];
          immEncoder := [];
          spec ty pc inst cs1 cs2 scr csr :=
              ( RetE ((DefFullOutput ty)
                        @%[ "exception?" <- $$true ]
                        @%[ "exceptionCause" <- Const ty (natToWord Xlen ECall) ]
                        @%[ "baseException?" <- $$true ]));
          instProperties := DefProperties<| hasCd := false |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |};
        {|instName := "MRet";
          uniqId := [fieldVal opcodeField (5'b"11100");
                     fieldVal rdFixedField (5'h"0");
                     fieldVal funct3Field (3'h"0");
                     fieldVal rs1FixedField (5'h"0");
                     fieldVal rs2FixedField (5'b"00010");
                     fieldVal funct7Field (7'b"0011000")];
          immEncoder := [];
          spec ty pc inst cs1 cs2 scr csr :=
            ( LETE pcPerms <- getCapPerms capAccessors (pc @% "cap");
              LETE mepcPerms <- getCapPerms capAccessors (scr @% "cap");
              LETC exceptionCause <- ITE (!(#pcPerms @% "SR"))
                                       (Const ty (natToWord Xlen CapSysRegViolation))
                                       (ITE (!(#mepcPerms @% "EX"))
                                          (Const ty (natToWord Xlen CapExecViolation))
                                          (Const ty (natToWord Xlen CapTagViolation)));
              LETC newMepc <- if compressed
                              then ZeroExtendTruncLsb Xlen
                                     ({< ZeroExtendTruncMsb (Xlen - 1) (scr @% "val"), $$WO~0 >})
                              else ZeroExtendTruncLsb Xlen
                                     ({< ZeroExtendTruncMsb (Xlen - 2) (scr @% "val"), $$(2'b"00") >});
              LETE representable <- representableFn (justFullCap scr) #newMepc;
              LETC exception <- !((scr @% "tag") && !isSealed capAccessors (scr @% "cap") && #representable
                                  && (#mepcPerms @% "EX") && (#pcPerms @% "SR"));
              RetE ((DefFullOutput ty)
                      @%[ "taken?" <- $$true ]
                      @%[ "changePcCap?" <- $$true ]
                      @%[ "pcMemAddr" <- #newMepc ]
                      @%[ "pcCap" <- scr @% "cap" ]
                      @%[ "exception?" <- #exception ]
                      @%[ "exceptionCause" <- #exceptionCause ]
                      @%[ "exceptionValue" <- #newMepc ]
                      @%[ "scrException?" <- !(#pcPerms @% "SR") ]
                      @%[ "pcCapException?" <- #pcPerms @% "SR" ]));
          instProperties := DefProperties<| implicitScr := MepccIndex |><| hasCd := false |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |}
      ]
    |}.

  Definition isECallInst ty (inst: Inst @# ty) :=
    redLet (@Kor _ _) (fun x => RetE (matchUniqId inst (uniqId x)))
      (filter (fun x => String.eqb (instName x) "ECall") (filterInsts [exceptionInsts])).

  Definition ExecRoot : ConstT FullCapWithTag := STRUCT_CONST { "tag" ::= true;
                                                                "cap" ::= ExecRootCap;
                                                                "val" ::= MtccVal }.

  Definition DataRoot : ConstT FullCapWithTag := STRUCT_CONST { "tag" ::= true;
                                                                "cap" ::= DataRootCap;
                                                                "val" ::= MtdcVal }.

  Definition SealRoot : ConstT FullCapWithTag := STRUCT_CONST { "tag" ::= true;
                                                                "cap" ::= SealRootCap;
                                                                "val" ::= $0 }.

  Definition scrList : list ScrReg :=
    let ZeroBits := if compressed then 1 else 2 in
    [ {|scrRegInfo := Build_RegInfo ($27)%word "MEPrevPCC" (Some (SyntaxConst DataRoot));
        isLegal ty val := isZero (ZeroExtendTruncLsb ZeroBits val);
        legalize ty val :=
          ZeroExtendTruncLsb Xlen ({< ZeroExtendTruncMsb (Xlen - ZeroBits) val, $$(wzero ZeroBits) >}) |};
      {|scrRegInfo := Build_RegInfo ($28)%word "MTCC" (Some (SyntaxConst ExecRoot));
        isLegal ty val := $$true;
        legalize ty val := val |};
      {|scrRegInfo := Build_RegInfo ($29)%word "MTDC" (Some (SyntaxConst DataRoot));
        isLegal ty val := isZero (ZeroExtendTruncLsb 2 val);
        legalize ty val := ZeroExtendTruncLsb Xlen ({< ZeroExtendTruncMsb (Xlen - 2) val, $$(wzero 2) >}) |};
      {|scrRegInfo := Build_RegInfo ($30)%word "MScratchC" (Some (SyntaxConst SealRoot));
        isLegal ty val := $$true;
        legalize ty val := val |};
      {|scrRegInfo := Build_RegInfo ($MepccIndex)%word "MEPCC" (Some (SyntaxConst ExecRoot));
        isLegal ty val := isZero (ZeroExtendTruncLsb ZeroBits val);
        legalize ty val :=
          ZeroExtendTruncLsb Xlen ({< ZeroExtendTruncMsb (Xlen - ZeroBits) val, $$(wzero ZeroBits) >}) |}
    ].

  Definition isValidScrs ty (inst : Inst @# ty) :=
    Kor (map (fun scr => rs2Fixed inst == Const ty (regAddr (scrRegInfo scr))) scrList).

  Definition legalizeScrs ty (inst : Inst @# ty) (cs1 : FullCapWithTag @# ty): FullCapWithTag @# ty :=
    Kor (map (fun '(Build_ScrReg regInfo islegal legalizer) =>
                let cs1Val := cs1 @% "val" in
                ITE (rs2Fixed inst == Const ty (regAddr regInfo))
                  ((STRUCT { "tag" ::= (cs1 @% "tag") && islegal _ (cs1 @% "val");
                             "cap" ::= cs1 @% "cap";
                             "val" ::= legalizer _ cs1Val }) : FullCapWithTag @# ty)
                  (Const _ Default)) scrList).

  Definition scrInsts: InstEntryFull FullOutput :=
    {|xlens := [32; 64];
      extension := Base;
      instEntries :=
        [ {|instName := ("CSpecialRW")%string;
            uniqId := [fieldVal opcodeField (truncMsb (5'h"5b"));
                       fieldVal funct3Field (3'h"0");
                       fieldVal funct7Field (7'h"1")];
            immEncoder := [];
            spec ty pc inst cs1 cs2 scr csr :=
              ( LETE pcPerms <- getCapPerms capAccessors (pc @% "cap");
                LETC legal <- isValidScrs inst;
                LETC fixCs1 <- legalizeScrs inst cs1;
                LETC tag <- (#fixCs1 @% "tag") && !isSealed capAccessors (#fixCs1 @% "cap");
                RetE ((DefWbFullOutput ty)
                        @%[ "cdTag" <- scr @% "tag" ]
                        @%[ "cdCap" <- scr @% "cap" ]
                        @%[ "cdVal" <- scr @% "val" ]
                        @%[ "exception?" <- !(#pcPerms @% "SR") || !#legal ]
                        @%[ "exceptionCause" <- (IF #legal
                                                 then Const ty (natToWord Xlen CapSysRegViolation)
                                                 else Const ty (natToWord Xlen InstIllegal))]
                        @%[ "wbScr?" <- isNotZero (rs1Fixed inst)]
                        @%[ "scrTag" <- #tag ]
                        @%[ "scrCap" <- #fixCs1 @% "cap" ]
                        @%[ "scrVal" <- #fixCs1 @% "val" ]
                        @%[ "baseException?" <- !#legal ]
                        @%[ "scrException?" <- #legal ]));
            instProperties :=
              DefProperties<| hasCs1 := true |><| hasScr := true |>;
            goodInstEncode := eq_refl;
            goodImmEncode := ltac:(eexists; cbv; eauto)
          |} ] 
    |}.

  Definition MStatusInit := if IeInit then Xlen 'h"8" else wzero Xlen.
  Definition MIEInit := @wconcat (Xlen - 8) 8 Xlen (if MeieInit then _ 'h"8" else wzero (Xlen - 8))
                          (wconcat (if MtieInit then _ 'h"8" else wzero 4)
                             (if MsieInit then _ 'h"8" else wzero 4)).

  Definition csrList : list CsrReg := [
      {|csrRegInfo := Build_RegInfo MStatusIndex "MStatus" (Some (SyntaxConst MStatusInit));
        isSystemCsr := true;
        csrMask := Some (Xlen 'h"8") |};
      {|csrRegInfo := Build_RegInfo (_ 'h"304") "MIE" (Some (SyntaxConst MIEInit));
        isSystemCsr := true;
        csrMask := Some (Xlen 'h"888") |};
      {|csrRegInfo := Build_RegInfo (_ 'h"342") "MCause" None;
        isSystemCsr := true;
        csrMask := None |};
      {|csrRegInfo := Build_RegInfo (_ 'h"343") "MTVal" None;
        isSystemCsr := true;
        csrMask := None |} ].
  
  Definition isValidCsrs ty (inst : Inst @# ty) :=
    Kor (map (fun csr => (imm inst == Const ty (regAddr (csrRegInfo csr)))%kami_expr) csrList).

  Inductive CsrOp := UpdCsr | SetCsr | ClearCsr.

  Definition mkCsrEntry (name: string) (isCs1: bool) (csrOp: CsrOp) (funct3Val: word (snd funct3Field)):
    InstEntry FullOutput.
    refine
      {|instName := name;
        uniqId := [fieldVal opcodeField (5'b"11100");
                   fieldVal funct3Field funct3Val];
        immEncoder := if isCs1 then [] else [Build_ImmEncoder (fst rs1FixedField) imm5];
        spec ty pc inst cs1 cs2 scr csr :=
          ( LETC val : Data <- if isCs1 then cs1 @% "val" else ZeroExtendTruncLsb Xlen (rs1Fixed inst);
            LETC illegal <- (!isValidCsrs inst ||
                               Kor (map (fun csrInfo => isNotZero (#val .& $$(match csrMask csrInfo with
                                                                                    | Some v => wnot v
                                                                                    | None => wzero _
                                                                              end))) csrList));
            LETC sysRegPermReq <- Kor (map (fun csrInfo => $$(isSystemCsr csrInfo) &&
                                                             (imm inst == $$(regAddr (csrRegInfo csrInfo)))) csrList);
            LETE pcPerms <- getCapPerms capAccessors (pc @% "cap");
            LETC sysRegPermViolation <- #sysRegPermReq && !(#pcPerms @% "SR");
            LETC exception <- #illegal || #sysRegPermViolation;
            LETC exceptionCause <- ITE #illegal $$(natToWord Xlen InstIllegal) $$(natToWord Xlen CapSysRegViolation);
            LETC baseException <- #illegal;
            RetE ((DefWbFullOutput ty)
                    @%[ "cdVal" <- csr ]
                    @%[ "exception?" <- #exception ]
                    @%[ "exceptionCause" <- #exceptionCause ]
                    @%[ "baseException?" <- #baseException ]
                    @%[ "wbCsr?" <- match csrOp with
                                    | UpdCsr => $$true
                                    | _ => isNotZero (rs1Fixed inst)
                                    end ]
                    @%[ "csrVal" <- match csrOp with
                                    | UpdCsr => #val
                                    | SetCsr => (csr .| #val)
                                    | ClearCsr => (csr .& ~(#val))
                                    end ] ) );
        instProperties := DefProperties<| hasCs1 := isCs1 |><| hasCsr := true |>;
        goodInstEncode := _;
        goodImmEncode := _
      |}; destruct isCs1; (reflexivity || eexists; cbv; eauto).
  Defined.

  Definition csrInsts: InstEntryFull FullOutput :=
    {|xlens := [32; 64];
      extension := Base;
      instEntries := [
        mkCsrEntry "CSRRW"   true   UpdCsr (3'b"001");
        mkCsrEntry "CSRRS"   true   SetCsr (3'b"010");
        mkCsrEntry "CSRRC"   true ClearCsr (3'b"011");
        mkCsrEntry "CSRRWI" false   UpdCsr (3'b"101");
        mkCsrEntry "CSRRSI" false   SetCsr (3'b"110");
        mkCsrEntry "CSRRCI" false ClearCsr (3'b"111")
      ]
    |}.
  
  Definition iFenceInsts: InstEntryFull FullOutput :=
    {|xlens := [32; 64];
      extension := Base;
      instEntries := [
        {|instName := "FenceI";
          uniqId := [fieldVal opcodeField (5'b"00011");
                     fieldVal rdFixedField (5'h"0");
                     fieldVal funct3Field (3'b"001");
                     fieldVal rs1FixedField (5'h"0");
                     fieldVal immField (12'h"0")];
          immEncoder := [];
          spec ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefFullOutput ty)
                      @%[ "fenceI?" <- $$true ] ));
          instProperties := DefProperties<| hasCd := false |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |}
      ]
    |}.

  Definition specFuncUnits : list FuncEntry := map mkFuncEntry [
      {|funcNameFull := "base";
        localFuncInputFull := FullOutput;
        localFuncFull ty x := RetE x;
        instsFull := [aluInsts; alu64Insts; capInsts; branchInsts;
                      ldInsts; ld32Insts; ld64Insts; stInsts; st32Insts; st64Insts;
                      jumpInsts; exceptionInsts; scrInsts; csrInsts; iFenceInsts]
      |}
    ].

  (* Run the following only if the uniqId, instName, immEncoder or instProperties field changes for any instruction.
     (Corrollary: every time a new instruction is added, it must be run)
   *)

  Ltac simplify_field field :=
    repeat match goal with
           | |- context [field ?P] =>
               let sth := fresh "sth" in
               let Heq_sth := fresh "Heq_sth" in
               remember (field P) as sth eqn: Heq_sth; simpl in Heq_sth; rewrite Heq_sth; clear Heq_sth sth
      end.

  Ltac simplify_insts :=
    cbn [filterInsts specFuncUnits concat map mkFuncEntry insts instsFull localFuncInputFull fold_left fold_right
           localFuncInput];
    pose proof extsHasBase;
    simplify_field (@extension procParams FullOutput);
    destruct (in_dec Extension_eq_dec Base supportedExts);
    [| unfold getBool; rewrite ?andb_false_r; simpl; auto; constructor];
    simplify_field (@xlens procParams FullOutput);
    let H := fresh in
    destruct (xlenIs32_or_64) as [H | H];
    repeat (rewrite H; simpl).

  Ltac checkUniq :=
    simplify_insts;
    repeat constructor; unfold In, not; intros;
    repeat match goal with
      | H: ?p \/ ?q |- _ => destruct H; try discriminate
      end; auto.

  (*
  Theorem uniqAluNames: NoDup (concat (map (fun x => map (@instName _ _) (insts x)) specFuncUnits)).
  Proof.
    checkUniq.
  Qed.

  Theorem uniqAluIds: NoDup (concat (map (fun x => map (@uniqId _ _) (insts x)) specFuncUnits)).
  Proof.
    checkUniq.
  Qed.
  *)
End InstBaseSpec.
