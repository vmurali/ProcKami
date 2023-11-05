Require Import Kami.AllNotations ProcKami.CheriTypes.
Require Import List.

Section InstSpec.
  Context `{procParams: ProcParams}.
  Local Open Scope kami_expr.

  Definition SpecOutput :=
    STRUCT_TYPE {
        "wb?" :: Bool;
        "cdTag" :: Bool;
        "cdCap" :: Cap;
        "cdVal" :: Data;
        "taken?" :: Bool;
        "takenPc" :: Addr;
        "takenPcCapChange?" :: Bool;
        "takenPcCap" :: Cap;
        "exception?" :: Bool;
        "exceptionCause" :: Data;
        "memAddr" :: Addr;
        "memCap?" :: Bool;
        "memSize" :: MemSize;
        "load?" :: Bool;
        "ldSigned?" :: Bool;
        "ldLG" :: Bool;
        "ldLM" :: Bool;
        "ldMC" :: Bool;
        "store?" :: Bool;
        "stData" :: FullCapWithTag }.

  Section ty.
    Variable ty: Kind -> Type.
    Definition DefSpecOutput: SpecOutput @# ty :=
      (Const _ (getDefaultConst _)).

    Definition Trunc32Signed m n (e: Bit n @# ty) :=
      SignExtendTruncLsb m (ZeroExtendTruncLsb 32 e).

    Definition Trunc32Unsigned m n (e: Bit n @# ty) :=
      ZeroExtendTruncLsb m (ZeroExtendTruncLsb 32 e).

    Definition Sub n (e1 e2: Bit n @# ty) :=
      e1 + ~e2 + $1.
  End ty.

  Definition baseSpecEntries: list (InstEntry SpecOutput SpecOutput) := [
      {|instName := "AddI";
        xlens := [32; 64];
        extensions := [Base];
        uniqId := [fieldVal opcodeField (5'b"00100");
                   fieldVal funct3Field (3'b"000")];
        inputXform ty pc inst cs1 cs2 ie :=
          ( RetE ((DefSpecOutput ty)
                    @%[ "wb?" <- $$true ]
                    @%[ "cdVal" <- (cs1 @% "val") + SignExtendTruncLsb Xlen (imm inst)]));
        outputXform ty (res: SpecOutput @# ty) :=
          ( RetE (mkIntReg (res @% "cdVal") (res @% "takenPcCap") (res @% "takenPc")));
        instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
      |};
      {|instName := "SLTI";
        xlens := [32; 64];
        extensions := [Base];
        uniqId := [fieldVal opcodeField (5'b"00100");
                   fieldVal funct3Field (3'b"010")];
        inputXform ty pc inst cs1 cs2 ie :=
          ( LETC in1 <- SignExtend 1 (cs1 @% "val");
            LETC in2 <- SignExtendTruncLsb (Xlen + 1) (imm inst);
            LETC res <- #in1 - #in2;
            LETC msb <- UniBit (TruncMsb Xlen 1) #res;
            RetE ((DefSpecOutput ty)
                    @%[ "wb?" <- $$true ]
                    @%[ "cdVal" <- ZeroExtendTruncLsb Xlen #msb]));
        outputXform ty (res: SpecOutput @# ty) :=
          ( RetE (mkIntReg (res @% "cdVal") (res @% "takenPcCap") (res @% "takenPc")));
        instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
      |};
      {|instName := "SLTIU";
        xlens := [32; 64];
        extensions := [Base];
        uniqId := [fieldVal opcodeField (5'b"00100");
                   fieldVal funct3Field (3'b"011")];
        inputXform ty pc inst cs1 cs2 ie :=
          ( LETC in1 <- ZeroExtend 1 (cs1 @% "val");
            LETC in2 <- ZeroExtendTruncLsb (Xlen + 1) (imm inst);
            LETC res <- #in1 - #in2;
            LETC msb <- UniBit (TruncMsb Xlen 1) #res;
            RetE ((DefSpecOutput ty)
                    @%[ "wb?" <- $$true ]
                    @%[ "cdVal" <- ZeroExtendTruncLsb Xlen #msb]));
        outputXform ty (res: SpecOutput @# ty) :=
          ( RetE (mkIntReg (res @% "cdVal") (res @% "takenPcCap") (res @% "takenPc")));
        instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
      |};
      {|instName := "XorI";
        xlens := [32; 64];
        extensions := [Base];
        uniqId := [fieldVal opcodeField (5'b"00100");
                   fieldVal funct3Field (3'b"100")];
        inputXform ty pc inst cs1 cs2 ie :=
          ( RetE ((DefSpecOutput ty)
                    @%[ "wb?" <- $$true ]
                    @%[ "cdVal" <- ((cs1 @% "val") .^ (SignExtendTruncLsb Xlen (imm inst))) ]));
        outputXform ty (res: SpecOutput @# ty) :=
          ( RetE (mkIntReg (res @% "cdVal") (res @% "takenPcCap") (res @% "takenPc")));
        instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
      |};
      {|instName := "OrI";
        xlens := [32; 64];
        extensions := [Base];
        uniqId := [fieldVal opcodeField (5'b"00100");
                   fieldVal funct3Field (3'b"110")];
        inputXform ty pc inst cs1 cs2 ie :=
          ( RetE ((DefSpecOutput ty)
                    @%[ "wb?" <- $$true ]
                    @%[ "cdVal" <- ((cs1 @% "val") .| (SignExtendTruncLsb Xlen (imm inst))) ]));
        outputXform ty (res: SpecOutput @# ty) :=
          ( RetE (mkIntReg (res @% "cdVal") (res @% "takenPcCap") (res @% "takenPc")));
        instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
      |};
      {|instName := "AndI";
        xlens := [32; 64];
        extensions := [Base];
        uniqId := [fieldVal opcodeField (5'b"00100");
                   fieldVal funct3Field (3'b"111")];
        inputXform ty pc inst cs1 cs2 ie :=
          ( RetE ((DefSpecOutput ty)
                    @%[ "wb?" <- $$true ]
                    @%[ "cdVal" <- ((cs1 @% "val") .& (SignExtendTruncLsb Xlen (imm inst))) ]));
        outputXform ty (res: SpecOutput @# ty) :=
          ( RetE (mkIntReg (res @% "cdVal") (res @% "takenPcCap") (res @% "takenPc")));
        instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
      |};
      {|instName := "SLLI";
        xlens := [32];
        extensions := [Base];
        uniqId := [fieldVal opcodeField (5'b"00100");
                   fieldVal funct3Field (3'b"001");
                   fieldVal funct7Field (7'b"0000000")];
        inputXform ty pc inst cs1 cs2 ie :=
          ( RetE ((DefSpecOutput ty)
                    @%[ "wb?" <- $$true ]
                    @%[ "cdVal" <- ((cs1 @% "val") <<
                                      (ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm inst)))]));
        outputXform ty (res: SpecOutput @# ty) :=
          ( RetE (mkIntReg (res @% "cdVal") (res @% "takenPcCap") (res @% "takenPc")));
        instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
      |};
      {|instName := "SRLI";
        xlens := [32];
        extensions := [Base];
        uniqId := [fieldVal opcodeField (5'b"00100");
                   fieldVal funct3Field (3'b"101");
                   fieldVal funct7Field (7'b"0000000")];
        inputXform ty pc inst cs1 cs2 ie :=
          ( RetE ((DefSpecOutput ty)
                    @%[ "wb?" <- $$true ]
                    @%[ "cdVal" <- UniBit (TruncLsb Xlen 1)
                                     ((ZeroExtend 1 (cs1 @% "val")) >>>
                                        (ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm inst)))]));
        outputXform ty (res: SpecOutput @# ty) :=
          ( RetE (mkIntReg (res @% "cdVal") (res @% "takenPcCap") (res @% "takenPc")));
        instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
      |};
      {|instName := "SRAI";
        xlens := [32];
        extensions := [Base];
        uniqId := [fieldVal opcodeField (5'b"00100");
                   fieldVal funct3Field (3'b"101");
                   fieldVal funct7Field (7'b"0100000")];
        inputXform ty pc inst cs1 cs2 ie :=
          ( RetE ((DefSpecOutput ty)
                    @%[ "wb?" <- $$true ]
                    @%[ "cdVal" <- UniBit (TruncLsb Xlen 1)
                                     ((SignExtend 1 (cs1 @% "val")) >>>
                                        (ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm inst)))]));
        outputXform ty (res: SpecOutput @# ty) :=
          ( RetE (mkIntReg (res @% "cdVal") (res @% "takenPcCap") (res @% "takenPc")));
        instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
      |};
      {|instName := "SLLI";
        xlens := [64];
        extensions := [Base];
        uniqId := [fieldVal opcodeField (5'b"00100");
                   fieldVal funct3Field (3'b"001");
                   fieldVal funct6Field (6'b"000000")];
        inputXform ty pc inst cs1 cs2 ie :=
          ( RetE ((DefSpecOutput ty)
                    @%[ "wb?" <- $$true ]
                    @%[ "cdVal" <- ((cs1 @% "val") <<
                                      (ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm inst)))]));
        outputXform ty (res: SpecOutput @# ty) :=
          ( RetE (mkIntReg (res @% "cdVal") (res @% "takenPcCap") (res @% "takenPc")));
        instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
      |};
      {|instName := "SRLI";
        xlens := [64];
        extensions := [Base];
        uniqId := [fieldVal opcodeField (5'b"00100");
                   fieldVal funct3Field (3'b"101");
                   fieldVal funct6Field (6'b"000000")];
        inputXform ty pc inst cs1 cs2 ie :=
          ( RetE ((DefSpecOutput ty)
                    @%[ "wb?" <- $$true ]
                    @%[ "cdVal" <- UniBit (TruncLsb Xlen 1)
                                     ((ZeroExtend 1 (cs1 @% "val")) >>>
                                        (ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm inst)))]));
        outputXform ty (res: SpecOutput @# ty) :=
          ( RetE (mkIntReg (res @% "cdVal") (res @% "takenPcCap") (res @% "takenPc")));
        instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
      |};
      {|instName := "SRAI";
        xlens := [64];
        extensions := [Base];
        uniqId := [fieldVal opcodeField (5'b"00100");
                   fieldVal funct3Field (3'b"101");
                   fieldVal funct6Field (6'b"010000")];
        inputXform ty pc inst cs1 cs2 ie :=
          ( RetE ((DefSpecOutput ty)
                    @%[ "wb?" <- $$true ]
                    @%[ "cdVal" <- UniBit (TruncLsb Xlen 1)
                                     ((SignExtend 1 (cs1 @% "val")) >>>
                                        (ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm inst)))]));
        outputXform ty (res: SpecOutput @# ty) :=
          ( RetE (mkIntReg (res @% "cdVal") (res @% "takenPcCap") (res @% "takenPc")));
        instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
      |};
      {|instName := "Add";
        xlens := [32; 64];
        extensions := [Base];
        uniqId := [fieldVal opcodeField (5'b"01100");
                   fieldVal funct3Field (3'b"000");
                   fieldVal funct7Field (7'b"0000000")];
        inputXform ty pc inst cs1 cs2 ie :=
          ( RetE ((DefSpecOutput ty)
                    @%[ "wb?" <- $$true ]
                    @%[ "cdVal" <- (cs1 @% "val") + (cs2 @% "val")]));
        outputXform ty (res: SpecOutput @# ty) :=
          ( RetE (mkIntReg (res @% "cdVal") (res @% "takenPcCap") (res @% "takenPc")));
        instProperties := {| hasCs1 := true; hasCs2 := true; implicit := 0 |}
      |};
      {|instName := "Sub";
        xlens := [32; 64];
        extensions := [Base];
        uniqId := [fieldVal opcodeField (5'b"01100");
                   fieldVal funct3Field (3'b"000");
                   fieldVal funct7Field (7'b"0100000")];
        inputXform ty pc inst cs1 cs2 ie :=
          ( RetE ((DefSpecOutput ty)
                    @%[ "wb?" <- $$true ]
                    @%[ "cdVal" <- Sub (cs1 @% "val") (cs2 @% "val")]));
        outputXform ty (res: SpecOutput @# ty) :=
          ( RetE (mkIntReg (res @% "cdVal") (res @% "takenPcCap") (res @% "takenPc")));
        instProperties := {| hasCs1 := true; hasCs2 := true; implicit := 0 |}
      |};
      {|instName := "SLT";
        xlens := [32; 64];
        extensions := [Base];
        uniqId := [fieldVal opcodeField (5'b"01100");
                   fieldVal funct3Field (3'b"010");
                   fieldVal funct7Field (7'b"0000000")];
        inputXform ty pc inst cs1 cs2 ie :=
          ( LETC in1 <- SignExtend 1 (cs1 @% "val");
            LETC in2 <- SignExtend 1 (cs2 @% "val");
            LETC res <- UniBit (TruncMsb Xlen 1) (#in1 + ~#in2 + $1);
            RetE ((DefSpecOutput ty)
                    @%[ "wb?" <- $$true ]
                    @%[ "cdVal" <- ZeroExtendTruncLsb Xlen #res]));
        outputXform ty (res: SpecOutput @# ty) :=
          ( RetE (mkIntReg (res @% "cdVal") (res @% "takenPcCap") (res @% "takenPc")));
        instProperties := {| hasCs1 := true; hasCs2 := true; implicit := 0 |}
      |};
      {|instName := "SLTU";
        xlens := [32; 64];
        extensions := [Base];
        uniqId := [fieldVal opcodeField (5'b"01100");
                   fieldVal funct3Field (3'b"011");
                   fieldVal funct7Field (7'b"0000000")];
        inputXform ty pc inst cs1 cs2 ie :=
          ( LETC in1 <- ZeroExtend 1 (cs1 @% "val");
            LETC in2 <- ZeroExtend 1 (cs2 @% "val");
            LETC res <- UniBit (TruncMsb Xlen 1) (#in1 + ~#in2 + $1);
            RetE ((DefSpecOutput ty)
                    @%[ "wb?" <- $$true ]
                    @%[ "cdVal" <- ZeroExtendTruncLsb Xlen #res]));
        outputXform ty (res: SpecOutput @# ty) :=
          ( RetE (mkIntReg (res @% "cdVal") (res @% "takenPcCap") (res @% "takenPc")));
        instProperties := {| hasCs1 := true; hasCs2 := true; implicit := 0 |}
      |};
      {|instName := "Xor";
        xlens := [32; 64];
        extensions := [Base];
        uniqId := [fieldVal opcodeField (5'b"01100");
                   fieldVal funct3Field (3'b"100");
                   fieldVal funct7Field (7'b"0000000")];
        inputXform ty pc inst cs1 cs2 ie :=
          ( RetE ((DefSpecOutput ty)
                    @%[ "wb?" <- $$true ]
                    @%[ "cdVal" <- (cs1 @% "val") .^ (cs2 @% "val")]));
        outputXform ty (res: SpecOutput @# ty) :=
          ( RetE (mkIntReg (res @% "cdVal") (res @% "takenPcCap") (res @% "takenPc")));
        instProperties := {| hasCs1 := true; hasCs2 := true; implicit := 0 |}
      |};
      {|instName := "Or";
        xlens := [32; 64];
        extensions := [Base];
        uniqId := [fieldVal opcodeField (5'b"01100");
                   fieldVal funct3Field (3'b"110");
                   fieldVal funct7Field (7'b"0000000")];
        inputXform ty pc inst cs1 cs2 ie :=
          ( RetE ((DefSpecOutput ty)
                    @%[ "wb?" <- $$true ]
                    @%[ "cdVal" <- (cs1 @% "val") .| (cs2 @% "val")]));
        outputXform ty (res: SpecOutput @# ty) :=
          ( RetE (mkIntReg (res @% "cdVal") (res @% "takenPcCap") (res @% "takenPc")));
        instProperties := {| hasCs1 := true; hasCs2 := true; implicit := 0 |}
      |};
      {|instName := "And";
        xlens := [32; 64];
        extensions := [Base];
        uniqId := [fieldVal opcodeField (5'b"01100");
                   fieldVal funct3Field (3'b"111");
                   fieldVal funct7Field (7'b"0000000")];
        inputXform ty pc inst cs1 cs2 ie :=
          ( RetE ((DefSpecOutput ty)
                    @%[ "wb?" <- $$true ]
                    @%[ "cdVal" <- (cs1 @% "val") .& (cs2 @% "val")]));
        outputXform ty (res: SpecOutput @# ty) :=
          ( RetE (mkIntReg (res @% "cdVal") (res @% "takenPcCap") (res @% "takenPc")));
        instProperties := {| hasCs1 := true; hasCs2 := true; implicit := 0 |}
      |};
      {|instName := "SLL";
        xlens := [32; 64];
        extensions := [Base];
        uniqId := [fieldVal opcodeField (5'b"01100");
                   fieldVal funct3Field (3'b"001");
                   fieldVal funct7Field (7'b"0000000")];
        inputXform ty pc inst cs1 cs2 ie :=
          ( RetE ((DefSpecOutput ty)
                    @%[ "wb?" <- $$true ]
                    @%[ "cdVal" <- (cs1 @% "val") <<
                                     (ZeroExtendTruncLsb (Nat.log2_up Xlen) (cs2 @% "val"))]));
        outputXform ty (res: SpecOutput @# ty) :=
          ( RetE (mkIntReg (res @% "cdVal") (res @% "takenPcCap") (res @% "takenPc")));
        instProperties := {| hasCs1 := true; hasCs2 := true; implicit := 0 |}
      |};
      {|instName := "SRL";
        xlens := [32; 64];
        extensions := [Base];
        uniqId := [fieldVal opcodeField (5'b"01100");
                   fieldVal funct3Field (3'b"101");
                   fieldVal funct7Field (7'b"0000000")];
        inputXform ty pc inst cs1 cs2 ie :=
          ( RetE ((DefSpecOutput ty)
                    @%[ "wb?" <- $$true ]
                    @%[ "cdVal" <- UniBit (TruncLsb Xlen 1)
                                     ((ZeroExtend 1 (cs1 @% "val")) >>>
                                        (ZeroExtendTruncLsb (Nat.log2_up Xlen) (cs2 @% "val")))]));
        outputXform ty (res: SpecOutput @# ty) :=
          ( RetE (mkIntReg (res @% "cdVal") (res @% "takenPcCap") (res @% "takenPc")));
        instProperties := {| hasCs1 := true; hasCs2 := true; implicit := 0 |}
      |};
      {|instName := "SRA";
        xlens := [32; 64];
        extensions := [Base];
        uniqId := [fieldVal opcodeField (5'b"01100");
                   fieldVal funct3Field (3'b"101");
                   fieldVal funct7Field (7'b"0100000")];
        inputXform ty pc inst cs1 cs2 ie :=
          ( RetE ((DefSpecOutput ty)
                    @%[ "wb?" <- $$true ]
                    @%[ "cdVal" <- UniBit (TruncLsb Xlen 1)
                                     ((SignExtend 1 (cs1 @% "val")) >>>
                                        (ZeroExtendTruncLsb (Nat.log2_up Xlen) (cs2 @% "val")))]));
        outputXform ty (res: SpecOutput @# ty) :=
          ( RetE (mkIntReg (res @% "cdVal") (res @% "takenPcCap") (res @% "takenPc")));
        instProperties := {| hasCs1 := true; hasCs2 := true; implicit := 0 |}
      |};
      {|instName := "AddIW";
        xlens := [64];
        extensions := [Base];
        uniqId := [fieldVal opcodeField (5'b"00110");
                   fieldVal funct3Field (3'b"000")];
        inputXform ty pc inst cs1 cs2 ie :=
          ( RetE ((DefSpecOutput ty)
                    @%[ "wb?" <- $$true ]
                    @%[ "cdVal" <- Trunc32Signed Xlen ((cs1 @% "val") + SignExtendTruncLsb Xlen (imm inst))]));
        outputXform ty (res: SpecOutput @# ty) :=
          ( RetE (mkIntReg (res @% "cdVal") (res @% "takenPcCap") (res @% "takenPc")));
        instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
      |};
      {|instName := "SLLIW";
        xlens := [64];
        extensions := [Base];
        uniqId := [fieldVal opcodeField (5'b"00110");
                   fieldVal funct3Field (3'b"001");
                   fieldVal funct7Field (7'b"0000000")];
        inputXform ty pc inst cs1 cs2 ie :=
          ( RetE ((DefSpecOutput ty)
                    @%[ "wb?" <- $$true ]
                    @%[ "cdVal" <- Trunc32Signed Xlen ((cs1 @% "val") <<
                                                   (ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm inst)))]));
        outputXform ty (res: SpecOutput @# ty) :=
          ( RetE (mkIntReg (res @% "cdVal") (res @% "takenPcCap") (res @% "takenPc")));
        instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
      |};
      {|instName := "SRLIW";
        xlens := [64];
        extensions := [Base];
        uniqId := [fieldVal opcodeField (5'b"00110");
                   fieldVal funct3Field (3'b"101");
                   fieldVal funct7Field (7'b"0000000")];
        inputXform ty pc inst cs1 cs2 ie :=
          ( RetE ((DefSpecOutput ty)
                    @%[ "wb?" <- $$true ]
                    @%[ "cdVal" <- (Trunc32Unsigned Xlen (cs1 @% "val")) >>>
                                     (ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm inst))]));
        outputXform ty (res: SpecOutput @# ty) :=
          ( RetE (mkIntReg (res @% "cdVal") (res @% "takenPcCap") (res @% "takenPc")));
        instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
      |};
      {|instName := "SRAIW";
        xlens := [64];
        extensions := [Base];
        uniqId := [fieldVal opcodeField (5'b"00110");
                   fieldVal funct3Field (3'b"101");
                   fieldVal funct7Field (7'b"0100000")];
        inputXform ty pc inst cs1 cs2 ie :=
          ( RetE ((DefSpecOutput ty)
                    @%[ "wb?" <- $$true ]
                    @%[ "cdVal" <- (Trunc32Signed Xlen (cs1 @% "val")) >>>
                                     (ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm inst))]));
        outputXform ty (res: SpecOutput @# ty) :=
          ( RetE (mkIntReg (res @% "cdVal") (res @% "takenPcCap") (res @% "takenPc")));
        instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
      |};
      {|instName := "AddW";
        xlens := [64];
        extensions := [Base];
        uniqId := [fieldVal opcodeField (5'b"01110");
                   fieldVal funct3Field (3'b"000");
                   fieldVal funct7Field (7'b"0000000")];
        inputXform ty pc inst cs1 cs2 ie :=
          ( RetE ((DefSpecOutput ty)
                    @%[ "wb?" <- $$true ]
                    @%[ "cdVal" <- Trunc32Signed Xlen ((cs1 @% "val") + (cs2 @% "val"))]));
        outputXform ty (res: SpecOutput @# ty) :=
          ( RetE (mkIntReg (res @% "cdVal") (res @% "takenPcCap") (res @% "takenPc")));
        instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
      |};
      {|instName := "SubW";
        xlens := [64];
        extensions := [Base];
        uniqId := [fieldVal opcodeField (5'b"01110");
                   fieldVal funct3Field (3'b"000");
                   fieldVal funct7Field (7'b"0100000")];
        inputXform ty pc inst cs1 cs2 ie :=
          ( RetE ((DefSpecOutput ty)
                    @%[ "wb?" <- $$true ]
                    @%[ "cdVal" <- Trunc32Signed Xlen (Sub (cs1 @% "val") (cs2 @% "val"))]));
        outputXform ty (res: SpecOutput @# ty) :=
          ( RetE (mkIntReg (res @% "cdVal") (res @% "takenPcCap") (res @% "takenPc")));
        instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
      |};
      {|instName := "SLLW";
        xlens := [64];
        extensions := [Base];
        uniqId := [fieldVal opcodeField (5'b"01110");
                   fieldVal funct3Field (3'b"001");
                   fieldVal funct7Field (7'b"0000000")];
        inputXform ty pc inst cs1 cs2 ie :=
          ( RetE ((DefSpecOutput ty)
                    @%[ "wb?" <- $$true ]
                    @%[ "cdVal" <- Trunc32Signed Xlen
                                     ((cs1 @% "val") <<
                                        (ZeroExtendTruncLsb (Nat.log2_up Xlen) (cs2 @% "val")))]));
        outputXform ty (res: SpecOutput @# ty) :=
          ( RetE (mkIntReg (res @% "cdVal") (res @% "takenPcCap") (res @% "takenPc")));
        instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
      |};
      {|instName := "SRLW";
        xlens := [64];
        extensions := [Base];
        uniqId := [fieldVal opcodeField (5'b"01110");
                   fieldVal funct3Field (3'b"101");
                   fieldVal funct7Field (7'b"0000000")];
        inputXform ty pc inst cs1 cs2 ie :=
          ( RetE ((DefSpecOutput ty)
                    @%[ "wb?" <- $$true ]
                    @%[ "cdVal" <- (Trunc32Unsigned Xlen (cs1 @% "val")) >>>
                                     (ZeroExtendTruncLsb (Nat.log2_up Xlen) (cs2 @% "val"))]));
        outputXform ty (res: SpecOutput @# ty) :=
          ( RetE (mkIntReg (res @% "cdVal") (res @% "takenPcCap") (res @% "takenPc")));
        instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
      |};
      {|instName := "SRAW";
        xlens := [64];
        extensions := [Base];
        uniqId := [fieldVal opcodeField (5'b"01110");
                   fieldVal funct3Field (3'b"101");
                   fieldVal funct7Field (7'b"0100000")];
        inputXform ty pc inst cs1 cs2 ie :=
          ( RetE ((DefSpecOutput ty)
                    @%[ "wb?" <- $$true ]
                    @%[ "cdVal" <- (Trunc32Signed Xlen (cs1 @% "val")) >>>
                                     (ZeroExtendTruncLsb (Nat.log2_up Xlen) (cs2 @% "val"))]));
        outputXform ty (res: SpecOutput @# ty) :=
          ( RetE (mkIntReg (res @% "cdVal") (res @% "takenPcCap") (res @% "takenPc")));
        instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
      |}
    ].
End InstSpec.
