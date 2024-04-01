Require Import Kami.AllNotations ProcKami.Cheriot.Lib ProcKami.Cheriot.Types.
Require Import RecordUpdate.RecordUpdate.

Section InstBaseSpec.
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
                        @%[ "cdVal" <- (cs1 @% "val") + SignExtendTo Xlen (imm inst)]));
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
                LETC in2 <- SignExtendTo (Xlen + 1) (imm inst);
                LETC res <- #in1 - #in2;
                LETC msb <- UniBit (TruncMsb Xlen 1) #res;
                RetE ((DefWbFullOutput ty)
                        @%[ "cdVal" <- ZeroExtendTo Xlen #msb]));
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
                LETC in2 <- ZeroExtendTo (Xlen + 1) (imm inst);
                LETC res <- #in1 - #in2;
                LETC msb <- UniBit (TruncMsb Xlen 1) #res;
                RetE ((DefWbFullOutput ty)
                        @%[ "cdVal" <- ZeroExtendTo Xlen #msb]));
            instProperties := DefProperties<| hasCs1 := true |><| signExt := false |>;
            goodInstEncode := eq_refl;
            goodImmEncode := ltac:(eexists; cbv; eauto)
          |};
          {|instName := "XorI";
            uniqId := [fieldVal opcodeField (5'b"00100");
                       fieldVal funct3Field (3'b"100")];
            immEncoder := [ Build_ImmEncoder (fst immField) imm12 ];
            spec ty pc inst cs1 cs2 scr csr :=
              ( RetE ((DefWbFullOutput ty)
                        @%[ "cdVal" <- ((cs1 @% "val") .^ (SignExtendTo Xlen (imm inst))) ]));
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
                        @%[ "cdVal" <- ((cs1 @% "val") .| (SignExtendTo Xlen (imm inst))) ]));
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
                        @%[ "cdVal" <- ((cs1 @% "val") .& (SignExtendTo Xlen (imm inst))) ]));
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
                                          (TruncLsbTo (Nat.log2_up Xlen) _ (imm inst)))]));
            instProperties := DefProperties<| hasCs1 := true |>;
            goodInstEncode := _;
            immEnd := if Xlen =? 32 then 5 else 6;
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
                                            (TruncLsbTo (Nat.log2_up Xlen) _ (imm inst)))]));
            instProperties := DefProperties<| hasCs1 := true |>;
            goodInstEncode := _;
            immEnd := if Xlen =? 32 then 5 else 6;
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
                                            (TruncLsbTo (Nat.log2_up Xlen) _ (imm inst)))]));
            instProperties := DefProperties<| hasCs1 := true |>;
            goodInstEncode := _;
            immEnd := if Xlen =? 32 then 5 else 6;
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
                LETC msb <- UniBit (TruncMsb Xlen 1) (#in1 - #in2);
                RetE ((DefWbFullOutput ty)
                        @%[ "cdVal" <- ZeroExtendTo Xlen #msb]));
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
                LETC msb <- UniBit (TruncMsb Xlen 1) (#in1 - #in2);
                RetE ((DefWbFullOutput ty)
                        @%[ "cdVal" <- ZeroExtendTo Xlen #msb]));
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
                                         (TruncLsbTo (Nat.log2_up Xlen) _ (cs2 @% "val"))]));
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
                                            (TruncLsbTo (Nat.log2_up Xlen) _ (cs2 @% "val")))]));
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
                                            (TruncLsbTo (Nat.log2_up Xlen) _ (cs2 @% "val")))]));
            instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>;
            goodInstEncode := eq_refl;
            goodImmEncode := ltac:(eexists; cbv; eauto)
          |};
          {|instName := "LUI";
            uniqId := [fieldVal opcodeField (5'b"01101")];
            immEncoder := [Build_ImmEncoder (fst auiLuiField) imm20_U];
            spec ty pc inst cs1 cs2 scr csr :=
              ( RetE ((DefWbFullOutput ty)
                        @%[ "cdVal" <- ({< auiLuiOffset inst, $$(wzero 12) >})]));
            instProperties := DefProperties;
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
                      @%[ "cdVal" <- Trunc32Signed Xlen ((cs1 @% "val") + SignExtendTo Xlen (imm inst))]));
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
                                                           (TruncLsbTo (Nat.log2_up Xlen) _ (imm inst)))]));
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
                                       (TruncLsbTo (Nat.log2_up Xlen) _ (imm inst))]));
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
                                       (TruncLsbTo (Nat.log2_up Xlen) _ (imm inst))]));
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
                                          (TruncLsbTo (Nat.log2_up Xlen) _ (cs2 @% "val")))]));
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
                                       (TruncLsbTo (Nat.log2_up Xlen) _ (cs2 @% "val"))]));
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
                                       (TruncLsbTo (Nat.log2_up Xlen) _ (cs2 @% "val"))]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |}
      ]
    |}.

  Definition setBounds ty (cs1: FullCapWithTag @# ty) (len: Data @# ty) (isExact: Bool @# ty): FullCapWithTag ## ty :=
    ( LETE baseTop <- getCapBaseTop (rmTag cs1);
      LETC baseBound <- (cs1 @% "val") >= (#baseTop @% "base");
      LETC topBound <- (ZeroExtend 1 (cs1 @% "val") + ZeroExtend 1 len) <= (#baseTop @% "top");
      LETE capBounds <- getCapBounds (cs1 @% "val") len;
      LETC E <- getCapEFromExp (#capBounds @% "exp");
      LETC newCap : Cap <- (cs1 @% "cap")
                             @%[ "B" <- #capBounds @% "B"]
                             @%[ "T" <- #capBounds @% "T"]
                             @%[ "E" <- #E ];
      RetE (STRUCT {
                "tag" ::= (cs1 @% "tag") && !isCapSealed (cs1 @% "cap") && (#baseBound && #topBound)
                          && (!isExact || (#capBounds @% "exact?"));
                "cap" ::= #newCap;
                "val" ::= cs1 @% "val" } : FullCapWithTag @# ty) ).

  Definition capInsts: InstEntryFull FullOutput :=
    {|xlens := [32; 64];
      extension := Base;
      instEntries := [
        {|instName := "AUICGP";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"7b"))];
          immEncoder := [Build_ImmEncoder (fst auiLuiField) imm20_U];
          spec ty pc inst cs1 cs2 scr csr :=
            ( LETC newAddr <- (cs1 @% "val") + ZeroExtendTo Xlen ({< auiLuiOffset inst, $$(wzero 11) >});
              LETE representable <- representableFnCap (rmTag cs1) #newAddr;
              RetE ((DefWbFullOutput ty)
                      @%[ "cdTag" <- (cs1 @% "tag") && !isCapSealed (cs1 @% "cap") && #representable ]
                      @%[ "cdCap" <- cs1 @% "cap" ]
                      @%[ "cdVal" <- #newAddr ]));
          instProperties := DefProperties<| implicitReg := getRegScrId cgp |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |};
        {|instName := "AUIPCC";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"17"))];
          immEncoder := [Build_ImmEncoder (fst auiLuiField) imm20_U];
          spec ty pc inst cs1 cs2 scr csr :=
            ( LETC newAddr <- (pc @% "val") + ZeroExtendTo Xlen ({< auiLuiOffset inst, $$(wzero 11) >});
              LETE representable <- representableFnCap pc #newAddr;
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
            ( LETC cs1Cap <- cs1 @% "cap";
              LETC perms <- getCapPerms (cs1 @% "cap");
              LETC newPerms <- unpack CapPerms (TruncLsbTo (size CapPerms) _
                                                  ((ZeroExtendTo Xlen (pack #perms)) .& (cs2 @% "val")));
              LETC newCap <- (cs1 @% "cap") @%[ "p" <- encodePerms #newPerms ];
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
            ( LETE baseTop <- getCapBaseTop (rmTag cs1);
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
            ( LETC cap <- cs1 @% "cap";
              RetE ((DefWbFullOutput ty)
                      @%[ "cdVal" <- pack #cap ]));
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
            ( LETE baseTop <- getCapBaseTop (rmTag cs1);
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
            ( LETC perms <- getCapPerms (cs1 @% "cap");
              RetE ((DefWbFullOutput ty)
                      @%[ "cdVal" <- ZeroExtendTo Xlen (pack #perms) ]));
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
                      @%[ "cdVal" <- ZeroExtendTo Xlen (pack (cs1 @% "tag")) ]));
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
            ( LETE baseTop <- getCapBaseTop (rmTag cs1);
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
            ( LETC oType <- cs1 @% "cap" @% "oType";
              RetE ((DefWbFullOutput ty)
                      @%[ "cdVal" <- ZeroExtendTo Xlen #oType ]));
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
              LETE representable <- representableFnCap (rmTag cs1) #newAddr;
              RetE ((DefWbFullOutput ty)
                      @%[ "cdTag" <- (cs1 @% "tag") && !isCapSealed (cs1 @% "cap") && #representable ]
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
            ( LETC newAddr <- (cs1 @% "val") + SignExtendTo Xlen (imm inst);
              LETE representable <- representableFnCap (rmTag cs1) #newAddr;
              RetE ((DefWbFullOutput ty)
                      @%[ "cdTag" <- (cs1 @% "tag") && !isCapSealed (cs1 @% "cap") && #representable ]
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
        {|instName := "CRAM";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal rs2FixedField (5'h"9");
                     fieldVal funct7Field (7'h"7f")];
          immEncoder := [];
          spec ty pc inst cs1 cs2 scr csr :=
            ( LETE capBounds <- getCapBounds ($0) (cs1 @% "val");
              LETC mask <- $$(wones Xlen) << (#capBounds @% "exp");
              RetE ((DefWbFullOutput ty)
                      @%[ "cdVal" <- #mask ]));
          instProperties := DefProperties<| hasCs1 := true |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |};
        {|instName := "CRRL";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal rs2FixedField (5'h"8");
                     fieldVal funct7Field (7'h"7f")];
          immEncoder := [];
          spec ty pc inst cs1 cs2 scr csr :=
            ( LETE capBounds <- getCapBounds ($0) (cs1 @% "val");
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
              LETE representable <- representableFnCap (rmTag cs1) #newAddr;
              RetE ((DefWbFullOutput ty)
                      @%[ "cdTag" <- (cs1 @% "tag") && !isCapSealed (cs1 @% "cap") && #representable ]
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
            ( LETE newCd <- setBounds cs1 (ZeroExtendTo Xlen (imm inst)) $$false;
              RetE ((DefWbFullOutput ty)
                      @%[ "cdTag" <- #newCd @% "tag" ]
                      @%[ "cdCap" <- #newCd @% "cap" ]
                      @%[ "cdVal" <- #newCd @% "val" ]));
          instProperties := DefProperties<| hasCs1 := true |><| signExt := false |>;
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
                      @%[ "cdVal" <- ZeroExtendTo Xlen (pack (#tagEq && #capEq && #valEq)) ]));
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
                      @%[ "cdCap" <- unpack Cap (cs2 @% "val") ]
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
            ( LETE baseTop <- getCapBaseTop (rmTag cs1);
              LETE baseTop2 <- getCapBaseTop (rmTag cs2);
              LETC baseBound <- (#baseTop2 @% "base") >= (#baseTop @% "base");
              LETC topBound <- (#baseTop2 @% "top") <= (#baseTop @% "top");
              LETC tagEq <- (cs1 @% "tag") == (cs2 @% "tag");
              LETC perms <- getCapPerms (cs1 @% "cap");
              LETC perms2 <- getCapPerms (cs2 @% "cap");
              LETC permsAnd <- unpack CapPerms (pack #perms .& pack #perms2);
              LETC permsSub <- #permsAnd == #perms2;
              RetE ((DefWbFullOutput ty)
                      @%[ "cdVal" <-
                            ZeroExtendTo Xlen (pack (#baseBound && #topBound && #tagEq && #permsSub)) ]));
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
            ( LETE baseTop2 <- getCapBaseTop (rmTag cs2);
              LETC baseBound <- (cs2 @% "val") >= (#baseTop2 @% "base");
              LETC topBound <- ZeroExtend 1 (cs2 @% "val") + $1 <= (#baseTop2 @% "top");
              LETC perms <- getCapPerms (cs1 @% "cap");
              LETC perms2 <- getCapPerms (cs2 @% "cap");
              LETC validSealAddr <- isCapSealAddr (cs2 @% "val") (#perms @% "EX");
              LETC newCap <- sealCap (cs1 @% "cap") (TruncLsbTo CapOTypeSz _ (cs2 @% "val"));
              RetE ((DefWbFullOutput ty)
                      @%[ "cdTag" <- (cs2 @% "tag") && !isCapSealed (cs2 @% "cap") &&
                                       (#baseBound && #topBound) && (cs1 @% "tag") &&
                                       !isCapSealed (cs1 @% "cap") && (#perms2 @% "SE") && #validSealAddr]
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
            ( LETE baseTop2 <- getCapBaseTop (rmTag cs2);
              LETC baseBound <- (cs2 @% "val") >= (#baseTop2 @% "base");
              LETC topBound <- ZeroExtend 1 (cs2 @% "val") + $1 <= (#baseTop2 @% "top");
              LETC oType <- cs1 @% "cap" @% "oType";
              LETC oTypeEq <- ZeroExtendTo Xlen #oType == (cs2 @% "val");
              LETC perms <- getCapPerms (cs1 @% "cap");
              LETC perms2 <- getCapPerms (cs2 @% "cap");
              LETC newPerms <- #perms @%[ "GL" <- #perms @% "GL" && #perms2 @% "GL" ];
              LETC newCapWithPerms <- (cs1 @% "cap") @%[ "p" <- encodePerms #newPerms];
              LETC newCap <- unsealCap #newCapWithPerms;
              RetE ((DefWbFullOutput ty)
                      @%[ "cdTag" <- (cs2 @% "tag") && !isCapSealed (cs2 @% "cap") &&
                                       (#baseBound && #topBound) && (cs1 @% "tag") &&
                                       isCapSealed (cs1 @% "cap") && (#perms2 @% "US") && #oTypeEq]
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
          ( LETC newAddr <- (pc @% "val") + SignExtendTo Xlen (branchOffset inst);
            LETE taken <- takenFn (cs1 @% "val") (cs2 @% "val");
            LETE representable <- representableFnCap (rmTag cs1) #newAddr;
            RetE ((DefFullOutput ty)
                    @%[ "taken?" <- #taken ]
                    @%[ "pcMemAddr" <- #newAddr ]
                    @%[ "exception?" <- if compressed
                                        then !#representable
                                        else !#representable || isNotZero (TruncLsbTo 2 _ #newAddr) ]
                    @%[ "exceptionCause" <- if compressed
                                            then Const ty (natToWord Xlen CapBoundsViolation)
                                            else (IF #representable
                                                  then Const ty (natToWord Xlen InstMisaligned)
                                                  else Const ty (natToWord Xlen CapBoundsViolation)) ]
                    @%[ "exceptionValue" <- #newAddr ]
                    @%[ "baseException?" <- #representable ]
                    @%[ "pcCapException?" <- !#representable ]));
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
        ( LETC newAddr <- (cs1 @% "val") + SignExtendTo Xlen (imm inst);
          LETE baseTop <- getCapBaseTop (rmTag cs1);
          LETC baseBound <- #newAddr >= (#baseTop @% "base");
          LETC topBound <- ZeroExtend 1 #newAddr + $size <= (#baseTop @% "top");
          LETC perms <- getCapPerms (cs1 @% "cap");
          LETC fullException
            : Maybe Data <-
                (IF !(cs1 @% "tag")
                 then Valid (Const ty (natToWord Xlen CapTagViolation))
                 else (IF isCapSealed (cs1 @% "cap")
                       then Valid (Const ty (natToWord Xlen CapSealViolation))
                       else (IF !(#perms @% "LD")
                             then Valid (Const ty (natToWord Xlen CapLdViolation))
                             else (IF !(#baseBound && #topBound)
                                   then Valid (Const ty (natToWord Xlen CapBoundsViolation))
                                   else StaticIf isCap
                                          (isNotZero (TruncLsbTo (Nat.log2_up ((Xlen + CapSz)/8)) _ #newAddr))
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
        ( LETC newAddr <- (cs1 @% "val") + SignExtendTo Xlen ({< funct7 inst, rdFixed inst >});
          LETE baseTop <- getCapBaseTop (rmTag cs1);
          LETC baseBound <- #newAddr >= (#baseTop @% "base");
          LETC topBound <- ZeroExtend 1 #newAddr + $size <= (#baseTop @% "top");
          LETC perms <- getCapPerms (cs1 @% "cap");
          LETC perms2 <- getCapPerms (cs2 @% "cap");
          LETC newTag <- (cs2 @% "tag") && ((#perms2 @% "GL") || (#perms @% "SL"));
          LETC fullException
            : Maybe Data <-
                (IF !(cs1 @% "tag")
                 then Valid (Const ty (natToWord Xlen CapTagViolation))
                 else (IF isCapSealed (cs1 @% "cap")
                       then Valid (Const ty (natToWord Xlen CapSealViolation))
                       else (IF !(#perms @% "SD")
                             then Valid (Const ty (natToWord Xlen CapStViolation))
                             else (IF !(#perms @% "MC")
                                   then Valid (Const ty (natToWord Xlen CapStCapViolation))
                                   else (IF !(#baseBound && #topBound)
                                         then Valid (Const ty (natToWord Xlen CapBoundsViolation))
                                         else StaticIf isCap
                                                (isNotZero
                                                   (TruncLsbTo (Nat.log2_up ((Xlen + CapSz)/8)) _ #newAddr))
                                                (Valid (Const ty (natToWord Xlen CapStMisaligned)))
                                                Invalid)))));
          RetE ((DefFullOutput ty)
                  @%[ "cdTag" <- #newTag ]
                  @%[ "cdCap" <- cs2 @% "cap" ]
                  @%[ "cdVal" <- cs2 @% "val" ]
                  @%[ "exception?" <- #fullException @% "valid" ]
                  @%[ "exceptionCause" <- #fullException @% "data" ]
                  @%[ "pcMemAddr" <- #newAddr ]
                  @%[ "memCap?" <- $$isCap ]
                  @%[ "memSize" <- Const ty (natToWord MemSizeSz size) ]
                  @%[ "mem?" <- $$true ]
                  @%[ "store?" <- $$true ] ));
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
  
  Definition jumpInsts: InstEntryFull FullOutput :=
    {|xlens := [32; 64];
      extension := Base;
      instEntries := [
        {|instName := "CJAL";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"6f"))];
          immEncoder := [Build_ImmEncoder (fst auiLuiField) imm20_J];
          spec ty pc inst cs1 cs2 scr csr :=
            ( LETC newAddr <- (pc @% "val") + SignExtendTo Xlen (jalOffset inst);
              LETC linkAddr <- (pc @% "val") + ITE (isInstNotCompressed inst) $4 $2;
              LETC mstatusArr <- unpack (Array Xlen Bool) csr;
              LETC ie <- #mstatusArr ![ 3 ];
              LETE representable <- representableFnCap pc #newAddr;
              RetE ((DefWbFullOutput ty)
                      @%[ "cdTag" <- $$true ]
                      @%[ "cdCap" <- sealCap (pc @% "cap") (getCapOTypeFromIe #ie) ]
                      @%[ "cdVal" <- #linkAddr ]
                      @%[ "taken?" <- $$true ]
                      @%[ "pcMemAddr" <- #newAddr ]
                      @%[ "exception?" <- if compressed
                                          then !#representable
                                          else !#representable || isNotZero (TruncLsbTo 2 _ #newAddr) ]
                      @%[ "exceptionCause" <- if compressed
                                              then Const ty (natToWord Xlen CapBoundsViolation)
                                              else (IF #representable
                                                    then Const ty (natToWord Xlen InstMisaligned)
                                                    else Const ty (natToWord Xlen CapBoundsViolation)) ]
                      @%[ "exceptionValue" <- #newAddr ]
                      @%[ "baseException?" <- #representable ]
                      @%[ "pcCapException?" <- !#representable ]));
          instProperties := DefProperties <| implicitCsr := getCsrId mstatus |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |};
        {|instName := "CJALR";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"67"));
                     fieldVal funct3Field (3'h"0")];
          immEncoder := [Build_ImmEncoder (fst immField) imm12];
          spec ty pc inst cs1 cs2 scr csr :=
            ( LETC newAddrTemp <- (cs1 @% "val") + SignExtendTo Xlen (imm inst);
              LETC newAddr <- ({< TruncMsbTo (Xlen - 1) 1 #newAddrTemp, $$WO~0 >});
              LETC linkAddr <- (pc @% "val") + ITE (isInstNotCompressed inst) $4 $2;
              LETC perms <- getCapPerms (cs1 @% "cap");
              LETE representable <- representableFnCap (rmTag cs1) #newAddr;
              LETC fullException
                : Pair (Maybe Data) Bool <-
                    (IF !(cs1 @% "tag")
                     then mkPair (Valid (Const ty (natToWord Xlen CapTagViolation))) ($$false)
                     else (IF isCapSealed (cs1 @% "cap") &&
                             (!isCapSentry (cs1 @% "cap") || isNotZero (imm inst) )
                           then mkPair (Valid (Const ty (natToWord Xlen CapSealViolation))) ($$false)
                           else (IF !(#perms @% "EX")
                                 then mkPair (Valid (Const ty (natToWord Xlen CapExecViolation))) ($$false)
                                 else (IF !#representable
                                       then mkPair (Valid (Const ty (natToWord Xlen CapBoundsViolation))) ($$false)
                                       else (StaticIf (negb compressed) (isNotZero (TruncLsbTo 2 _ #newAddr))
                                               (mkPair (Valid (Const ty (natToWord Xlen InstMisaligned))) ($$true))
                                               (mkPair Invalid ($$false)))))));
              LETC mstatusArr <- unpack (Array Xlen Bool) csr;
              LETC ie <- #mstatusArr ![ 3 ];
              LETC ieSentry <- isCapIeSentry (cs1 @% "cap");
              LETC idSentry <- isCapIdSentry (cs1 @% "cap");
              LETC mstatusArr <- unpack (Array Xlen Bool) csr;
              LETC newMStatus <- UpdateArrayConst #mstatusArr (@natToFin 3 _) #ieSentry;
              RetE ((DefWbFullOutput ty)
                      @%[ "cdTag" <- $$true ]
                      @%[ "cdCap" <- sealCap (pc @% "cap") (getCapOTypeFromIe #ie) ]
                      @%[ "cdVal" <- #linkAddr ]
                      @%[ "taken?" <- $$true ]
                      @%[ "pcMemAddr" <- #newAddr ]
                      @%[ "changePcCap?" <- $$true ]
                      @%[ "pcCap" <- unsealCap (cs1 @% "cap") ]
                      @%[ "exception?" <- #fullException @% "fst" @% "valid" ]
                      @%[ "exceptionCause" <- #fullException @% "fst" @% "data" ]
                      @%[ "exceptionValue" <- #newAddr ]
                      @%[ "baseException?" <- #fullException @% "snd" ]
                      @%[ "wbCsr?" <- #ieSentry || #idSentry ]
                      @%[ "csrVal" <- pack #newMStatus ] ));
          instProperties := DefProperties<| hasCs1 := true |><| implicitCsr := getCsrId mstatus |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |}
      ]
    |}.

  Definition isJumpInsts ty (inst: Inst @# ty) :=
    redLet (@Kor _ _) (fun x => RetE (matchUniqId inst (uniqId x))) (filterInsts [jumpInsts]).


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
            ( LETC pcPerms <- getCapPerms (pc @% "cap");
              LETC mepcPerms <- getCapPerms (scr @% "cap");
              LETC exceptionCause <- ITE (!(#pcPerms @% "SR"))
                                       (Const ty (natToWord Xlen CapSysRegViolation))
                                       (ITE (!(#mepcPerms @% "EX"))
                                          (Const ty (natToWord Xlen CapExecViolation))
                                          (Const ty (natToWord Xlen CapTagViolation)));
              LETC newMepc <- if compressed
                              then ({< TruncMsbTo (Xlen - 1) 1 (scr @% "val"), $$WO~0 >})
                              else ({< TruncMsbTo (Xlen - 2) 2 (scr @% "val"), $$(2'b"00") >});
              LETE representable <- representableFnCap (rmTag scr) #newMepc;
              LETC exception <- !((scr @% "tag") && !isCapSealed (scr @% "cap") && #representable
                                  && (#mepcPerms @% "EX") && (#pcPerms @% "SR"));
              LETC mstatusArr <- unpack (Array Xlen Bool) csr;
              LETC pie <- #mstatusArr ![ 7 ];
              LETC newMStatus <- UpdateArrayConst #mstatusArr (@natToFin 3 _) #pie;
              RetE ((DefFullOutput ty)
                      @%[ "taken?" <- $$true ]
                      @%[ "changePcCap?" <- $$true ]
                      @%[ "pcMemAddr" <- #newMepc ]
                      @%[ "pcCap" <- scr @% "cap" ]
                      @%[ "exception?" <- #exception ]
                      @%[ "exceptionCause" <- #exceptionCause ]
                      @%[ "exceptionValue" <- #newMepc ]
                      @%[ "scrException?" <- !(#pcPerms @% "SR") ]
                      @%[ "pcCapException?" <- #pcPerms @% "SR" ]
                      @%[ "wbCsr?" <- $$true]
                      @%[ "csrVal" <- pack #newMStatus ]));
          instProperties := DefProperties
                              <| implicitScr := getRegScrId mepcc |>
                                                  <| implicitCsr := getCsrId mstatus |><| hasCd := false |>;
          goodInstEncode := eq_refl;
          goodImmEncode := ltac:(eexists; cbv; eauto)
        |}
      ]
    |}.

  Definition isECallInst ty (inst: Inst @# ty) :=
    redLet (@Kor _ _) (fun x => RetE (matchUniqId inst (uniqId x)))
      (filter (fun x => String.eqb (instName x) "ECall") (filterInsts [exceptionInsts])).

  Definition scrList : list ScrReg :=
    let ZeroBits := if compressed then 1 else 2 in
    [ {|scrRegInfo := Build_RegInfo (getRegScrId mtcc) mtccReg;
        isLegal ty val := $$true;
        legalize ty val := val |};
      {|scrRegInfo := Build_RegInfo (getRegScrId mtdc) mtdcReg;
        isLegal ty val := isZero (TruncLsbTo 2 _ val);
        legalize ty val := ({< TruncMsbTo (Xlen - 2) 2 val, $$(wzero 2) >}) |};
      {|scrRegInfo := Build_RegInfo (getRegScrId mscratchc) mScratchCReg;
        isLegal ty val := $$true;
        legalize ty val := val |};
      {|scrRegInfo := Build_RegInfo (getRegScrId mepcc) mepccReg;
        isLegal ty val := isZero (TruncLsbTo ZeroBits _ val);
        legalize ty val :=
          ({< TruncMsbTo (Xlen - ZeroBits) ZeroBits val, $$(wzero ZeroBits) >}) |}
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
           uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                      fieldVal funct3Field (3'h"0");
                      fieldVal funct7Field (7'h"1")];
           immEncoder := [];
           spec ty pc inst cs1 cs2 scr csr :=
             ( LETC pcPerms <- getCapPerms (pc @% "cap");
               LETC legal <- isValidScrs inst;
               LETC fixCs1 <- legalizeScrs inst cs1;
               LETC isWriteScr <- isNotZero (rs1 inst);
               LETC tag <- (#fixCs1 @% "tag") && !isCapSealed (#fixCs1 @% "cap");
               RetE ((DefWbFullOutput ty)
                       @%[ "cdTag" <- scr @% "tag" ]
                       @%[ "cdCap" <- scr @% "cap" ]
                       @%[ "cdVal" <- scr @% "val" ]
                       @%[ "exception?" <- !(#pcPerms @% "SR") || !#legal ]
                       @%[ "exceptionCause" <- (IF #legal
                                                then Const ty (natToWord Xlen CapSysRegViolation)
                                                else Const ty (natToWord Xlen InstIllegal))]
                       @%[ "wbScr?" <- isNotZero (rs1Fixed inst)]
                       @%[ "scrTag" <- ITE #isWriteScr #tag (scr @% "tag") ]
                       @%[ "scrCap" <- ITE #isWriteScr (#fixCs1 @% "cap") (scr @% "cap") ]
                       @%[ "scrVal" <- ITE #isWriteScr (#fixCs1 @% "val") (scr @% "val") ]
                       @%[ "baseException?" <- !#legal ]
                       @%[ "scrException?" <- #legal ]));
           instProperties :=
             DefProperties<| hasCs1 := true |><| hasScr := true |>;
                                                             goodInstEncode := eq_refl;
           goodImmEncode := ltac:(eexists; cbv; eauto)
         |} ] 
   |}.

  Definition MStatusInit := if IeInit then Xlen 'h"8" else wzero Xlen.
  Definition MIEInit : word Xlen := evalExpr (ZeroExtend (Xlen - 12)
                                                ({<if MeieInit then Const type (4'h"8") else $0,
                                                    if MtieInit then Const type (4'h"8") else $0,
                                                    if MsieInit then Const type (4'h"8") else $0>})).

  Definition csrList : list CsrReg := [
      {|csrRegInfo := Build_RegInfo (getCsrId mstatus) mStatusReg;
        isSystemCsr := true;
        csrMask := Some (Xlen 'h"88") |};
      {|csrRegInfo := Build_RegInfo (getCsrId mie) mieReg;
        isSystemCsr := true;
        csrMask := Some (Xlen 'h"888") |};
      {|csrRegInfo := Build_RegInfo (getCsrId mcause) mCauseReg;
        isSystemCsr := true;
        csrMask := None |};
      {|csrRegInfo := Build_RegInfo (getCsrId mtval) mtValReg;
        isSystemCsr := true;
        csrMask := None |} ].
  
  Definition isValidCsrs ty (inst : Inst @# ty) :=
    Kor (map (fun csr => (imm inst == Const ty (regAddr (csrRegInfo csr)))%kami_expr) csrList).

  Inductive CsrOp := UpdCsr | SetCsr | ClearCsr.

  Definition mkCsrEntry (name: string) (isCs1: bool) (csrOp: CsrOp) (funct3Val: word (snd funct3Field)):
    InstEntrySpec.
    refine
      {|instName := name;
        uniqId := [fieldVal opcodeField (5'b"11100");
                   fieldVal funct3Field funct3Val];
        immEncoder := if isCs1 then [] else [Build_ImmEncoder (fst rs1FixedField) imm5];
        spec ty pc inst cs1 cs2 scr csr :=
          ( LETC val : Data <- if isCs1 then cs1 @% "val" else ZeroExtendTo Xlen (rs1Fixed inst);
            LETC illegal <- (!isValidCsrs inst ||
                               Kor (map (fun csrInfo => isNotZero (#val .& $$(match csrMask csrInfo with
                                                                                    | Some v => wnot v
                                                                                    | None => wzero _
                                                                              end))) csrList));
            LETC sysRegPermReq <- Kor (map (fun csrInfo => $$(isSystemCsr csrInfo) &&
                                                             (imm inst == $$(regAddr (csrRegInfo csrInfo)))) csrList);
            LETC pcPerms <- getCapPerms (pc @% "cap");
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
        instProperties := DefProperties<| hasCs1 := isCs1 |><| hasCsr := true |><| signExt := false |>;
        goodInstEncode := _;
        immEnd := if isCs1 then 0 else 5;
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
                      ldInsts; ld32Insts; ld64Insts; stInsts; st32Insts;
                      jumpInsts; exceptionInsts; scrInsts; csrInsts; iFenceInsts]
      |}
    ].

  Fixpoint isDifferingBoolList (a b: list (option bool)) :=
    match a, b with
    | x :: xs, y :: ys => match x, y with
                          | Some p, Some q => orb (negb (Bool.eqb p q)) (isDifferingBoolList xs ys)
                          | _, _ => isDifferingBoolList xs ys
                          end
    | _, _ => false
    end.

  Fixpoint wordToOptBoolList n (w: word n) :=
    match n with
    | 0 => nil
    | S m => Some (Z.eqb (wordVal 1 (@truncLsb 1 _ w)) 1) :: wordToOptBoolList (@truncMsb m _ w)
    end.

  Local Fixpoint sortedUIdToOptBoolList (curr: nat) (sortedUId: UniqId) :=
    match sortedUId with
    | existT (pos, width) w :: xs =>
        repeat None (pos - curr) ++ wordToOptBoolList w ++ sortedUIdToOptBoolList (pos + width) xs
    | nil => nil
    end.

  Definition uniqIdToOptBoolList (u: UniqId) :=
    sortedUIdToOptBoolList 0 (SigWordSort.sort u).

  Ltac unfoldXlensExtension x :=
    match x with
    | context [xlens ?P] => let y := eval cbn [xlens P] in x in unfoldXlensExtension y
    | context [extension ?P] => let y := eval cbn [extension P] in x in unfoldXlensExtension y
    | _ => exact x
    end.

  Ltac unfoldInstEntries x :=
    match x with
    | context [instEntries ?P] => let y := eval cbn [instEntries P] in x in unfoldInstEntries y
    | _ => exact x
    end.
  
  Definition specInstEntries: list InstEntrySpec :=
    ltac:(let x := 
            eval cbv [filterInsts specFuncUnits concat map mkFuncEntry insts instsFull localFuncInputFull fold_left
                        fold_right localFuncInput uniqIdToOptBoolList sortedUIdToOptBoolList
                        wordToOptBoolList isDifferingBoolList] in specFuncUnits in
            match x with
            | [ {| insts := ?ins |} ] =>
                let y := eval cbn [Xlen orb andb Extension_eqb Nat.eqb existsb supportedExts] in
                ltac:(unfoldXlensExtension ins) in
                  let z := eval cbn [app] in ltac:(unfoldInstEntries y) in exact z
            end).

  Theorem uniqAluIds:
    ForallOrdPairsEval isDifferingBoolList (map (fun y => uniqIdToOptBoolList (uniqId y)) specInstEntries) = true.
  Proof.
    auto.
  Qed.

  Theorem uniqAluNames: NoDupEval (String.eqb) (map (@instName _) specInstEntries) = true.
  Proof.
    auto.
  Qed.
End InstBaseSpec.
