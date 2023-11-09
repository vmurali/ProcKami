Require Import Kami.AllNotations ProcKami.CheriTypes ProcKami.Lib.

Section InstBaseSpec.
  Context `{procParams: ProcParams}.
  Local Open Scope kami_expr.

  Definition BaseOutput :=
    STRUCT_TYPE {
        "wb?" :: Bool;
        "cdTag" :: Bool;
        "cdCap" :: Cap;
        "cdVal" :: Data;
        "mayChangePc?" :: Bool;
        "taken?" :: Bool;
        "pcMemAddr" :: Addr;
        "changePcCap?" :: Bool;
        "pcCap" :: Cap;
        "changeIe?" :: Bool;
        "newIe" :: Bool;
        "exception?" :: Bool;
        "exceptionCause" :: Data;
        "exceptionCausePc?" :: Bool;
        "mem?" :: Bool;
        "memCap?" :: Bool;
        "memSize" :: MemSize;
        "store?" :: Bool;
        "ldSigned?" :: Bool;
        "ldPerms" :: CapPerms;
        "interrupt?" :: Bool }.

  Section ty.
    Variable ty: Kind -> Type.
    Definition DefBaseOutput: BaseOutput @# ty := Const _ Default.

    Definition baseOutputXform (inp: BaseOutput @# ty): FuncOutput ## ty :=
      ( LETC memOp : MemOpInfo <-
                       STRUCT {
                           "op" ::= ITE (inp @% "store?") $StOp $LdOp;
                           "size" ::= inp @% "memSize";
                           "MC" ::= inp @% "ldPerms" @% "MC";
                           "LM" ::= inp @% "ldPerms" @% "LM";
                           "LG" ::= inp @% "ldPerms" @% "LG";
                           "sign?" ::= inp @% "ldSigned?";
                           "cap?" ::= inp @% "memCap?" };
        LETC cd : FullCapWithTag <-
                    STRUCT {
                        "tag" ::= inp @% "cdTag";
                        "cap" ::= inp @% "cdCap";
                        "val" ::= (IF (inp @% "exception?") || (inp @% "interrupt?")
                                   then inp @% "exceptionCause"
                                   else inp @% "cdVal") };
        RetE (STRUCT {
                  "data" ::= #cd;
                  "pcCapOrMemOp" ::= ITE (inp @% "mem?")
                                       (ZeroExtendTruncLsb CapSz (pack #memOp))
                                       (inp @% "pcCap");
                  "addr" ::= (inp @% "pcMemAddr");
                  "wb?" ::= inp @% "wb?";
                  "mayChangePc?" ::= inp @% "mayChangePc?";
                  "taken?" ::= inp @% "taken?";
                  "changePcCap?" ::= inp @% "changePcCap?";
                  "mem?" ::= inp @% "mem?";
                  "exception?" ::= inp @% "exception?";
                  "exceptionCausePc?" ::= inp @% "exceptionCausePc?";
                  "interrupt?" ::= inp @% "interrupt?";
                  "changeIe?" ::= inp @% "changeIe?";
                  "newIe" ::= inp @% "newIe" } : FuncOutput @# ty) ).
  End ty.

  Definition aluInsts: InstEntryFull BaseOutput :=
    {|xlens := [32; 64];
      extension := Base;
      instEntries := [
        {|instName := "AddI";
          uniqId := [fieldVal opcodeField (5'b"00100");
                     fieldVal funct3Field (3'b"000")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- (cs1 @% "val") + SignExtendTruncLsb Xlen (imm inst)]));
          instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
        |};
        {|instName := "SLTI";
          uniqId := [fieldVal opcodeField (5'b"00100");
                     fieldVal funct3Field (3'b"010")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( LETC in1 <- SignExtend 1 (cs1 @% "val");
              LETC in2 <- SignExtendTruncLsb (Xlen + 1) (imm inst);
              LETC res <- #in1 - #in2;
              LETC msb <- UniBit (TruncMsb Xlen 1) #res;
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- ZeroExtendTruncLsb Xlen #msb]));
          instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
        |};
        {|instName := "SLTIU";
          uniqId := [fieldVal opcodeField (5'b"00100");
                     fieldVal funct3Field (3'b"011")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( LETC in1 <- ZeroExtend 1 (cs1 @% "val");
              LETC in2 <- ZeroExtendTruncLsb (Xlen + 1) (imm inst);
              LETC res <- #in1 - #in2;
              LETC msb <- UniBit (TruncMsb Xlen 1) #res;
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- ZeroExtendTruncLsb Xlen #msb]));
          instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
        |};
        {|instName := "XorI";
          uniqId := [fieldVal opcodeField (5'b"00100");
                     fieldVal funct3Field (3'b"100")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- ((cs1 @% "val") .^ (SignExtendTruncLsb Xlen (imm inst))) ]));
          instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
        |};
        {|instName := "OrI";
          uniqId := [fieldVal opcodeField (5'b"00100");
                     fieldVal funct3Field (3'b"110")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- ((cs1 @% "val") .| (SignExtendTruncLsb Xlen (imm inst))) ]));
          instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
        |};
        {|instName := "AndI";
          uniqId := [fieldVal opcodeField (5'b"00100");
                     fieldVal funct3Field (3'b"111")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- ((cs1 @% "val") .& (SignExtendTruncLsb Xlen (imm inst))) ]));
          instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
        |};
        {|instName := "SLLI";
          uniqId := [fieldVal opcodeField (5'b"00100");
                     fieldVal funct3Field (3'b"001");
                     if Xlen =? 32
                     then fieldVal funct7Field (7'b"0000000")
                     else fieldVal funct6Field (6'b"000000")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- ((cs1 @% "val") <<
                                        (ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm inst)))]));
          instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
        |};
        {|instName := "SRLI";
          uniqId := [fieldVal opcodeField (5'b"00100");
                     fieldVal funct3Field (3'b"101");
                     if Xlen =? 32
                     then fieldVal funct7Field (7'b"0000000")
                     else fieldVal funct6Field (6'b"000000")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- UniBit (TruncLsb Xlen 1)
                                       ((ZeroExtend 1 (cs1 @% "val")) >>>
                                          (ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm inst)))]));
          instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
        |};
        {|instName := "SRAI";
          uniqId := [fieldVal opcodeField (5'b"00100");
                     fieldVal funct3Field (3'b"101");
                     if Xlen =? 32
                     then fieldVal funct7Field (7'b"0100000")
                     else fieldVal funct6Field (6'b"010000")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- UniBit (TruncLsb Xlen 1)
                                       ((SignExtend 1 (cs1 @% "val")) >>>
                                          (ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm inst)))]));
          instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
        |};
        {|instName := "Add";
          uniqId := [fieldVal opcodeField (5'b"01100");
                     fieldVal funct3Field (3'b"000");
                     fieldVal funct7Field (7'b"0000000")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- (cs1 @% "val") + (cs2 @% "val")]));
          instProperties := {| hasCs1 := true; hasCs2 := true; implicit := 0 |}
        |};
        {|instName := "Sub";
          uniqId := [fieldVal opcodeField (5'b"01100");
                     fieldVal funct3Field (3'b"000");
                     fieldVal funct7Field (7'b"0100000")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- (cs1 @% "val") - (cs2 @% "val")]));
          instProperties := {| hasCs1 := true; hasCs2 := true; implicit := 0 |}
        |};
        {|instName := "SLT";
          uniqId := [fieldVal opcodeField (5'b"01100");
                     fieldVal funct3Field (3'b"010");
                     fieldVal funct7Field (7'b"0000000")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( LETC in1 <- SignExtend 1 (cs1 @% "val");
              LETC in2 <- SignExtend 1 (cs2 @% "val");
              LETC res <- UniBit (TruncMsb Xlen 1) (#in1 - #in2);
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- ZeroExtendTruncLsb Xlen #res]));
          instProperties := {| hasCs1 := true; hasCs2 := true; implicit := 0 |}
        |};
        {|instName := "SLTU";
          uniqId := [fieldVal opcodeField (5'b"01100");
                     fieldVal funct3Field (3'b"011");
                     fieldVal funct7Field (7'b"0000000")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( LETC in1 <- ZeroExtend 1 (cs1 @% "val");
              LETC in2 <- ZeroExtend 1 (cs2 @% "val");
              LETC res <- UniBit (TruncMsb Xlen 1) (#in1 - #in2);
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- ZeroExtendTruncLsb Xlen #res]));
          instProperties := {| hasCs1 := true; hasCs2 := true; implicit := 0 |}
        |};
        {|instName := "Xor";
          uniqId := [fieldVal opcodeField (5'b"01100");
                     fieldVal funct3Field (3'b"100");
                     fieldVal funct7Field (7'b"0000000")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- (cs1 @% "val") .^ (cs2 @% "val")]));
          instProperties := {| hasCs1 := true; hasCs2 := true; implicit := 0 |}
        |};
        {|instName := "Or";
          uniqId := [fieldVal opcodeField (5'b"01100");
                     fieldVal funct3Field (3'b"110");
                     fieldVal funct7Field (7'b"0000000")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- (cs1 @% "val") .| (cs2 @% "val")]));
          instProperties := {| hasCs1 := true; hasCs2 := true; implicit := 0 |}
        |};
        {|instName := "And";
          uniqId := [fieldVal opcodeField (5'b"01100");
                     fieldVal funct3Field (3'b"111");
                     fieldVal funct7Field (7'b"0000000")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- (cs1 @% "val") .& (cs2 @% "val")]));
          instProperties := {| hasCs1 := true; hasCs2 := true; implicit := 0 |}
        |};
        {|instName := "SLL";
          uniqId := [fieldVal opcodeField (5'b"01100");
                     fieldVal funct3Field (3'b"001");
                     fieldVal funct7Field (7'b"0000000")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- (cs1 @% "val") <<
                                       (ZeroExtendTruncLsb (Nat.log2_up Xlen) (cs2 @% "val"))]));
          instProperties := {| hasCs1 := true; hasCs2 := true; implicit := 0 |}
        |};
        {|instName := "SRL";
          uniqId := [fieldVal opcodeField (5'b"01100");
                     fieldVal funct3Field (3'b"101");
                     fieldVal funct7Field (7'b"0000000")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- UniBit (TruncLsb Xlen 1)
                                       ((ZeroExtend 1 (cs1 @% "val")) >>>
                                          (ZeroExtendTruncLsb (Nat.log2_up Xlen) (cs2 @% "val")))]));
          instProperties := {| hasCs1 := true; hasCs2 := true; implicit := 0 |}
        |};
        {|instName := "SRA";
          uniqId := [fieldVal opcodeField (5'b"01100");
                     fieldVal funct3Field (3'b"101");
                     fieldVal funct7Field (7'b"0100000")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- UniBit (TruncLsb Xlen 1)
                                       ((SignExtend 1 (cs1 @% "val")) >>>
                                          (ZeroExtendTruncLsb (Nat.log2_up Xlen) (cs2 @% "val")))]));
          instProperties := {| hasCs1 := true; hasCs2 := true; implicit := 0 |}
        |}
      ]
    |}.

  Definition alu64Insts: InstEntryFull BaseOutput :=
    {|xlens := [64];
      extension := Base;
      instEntries := [
        {|instName := "AddIW";
          uniqId := [fieldVal opcodeField (5'b"00110");
                     fieldVal funct3Field (3'b"000")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- Trunc32Signed Xlen ((cs1 @% "val") + SignExtendTruncLsb Xlen (imm inst))]));
          instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
        |};
        {|instName := "SLLIW";
          uniqId := [fieldVal opcodeField (5'b"00110");
                     fieldVal funct3Field (3'b"001");
                     fieldVal funct7Field (7'b"0000000")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- Trunc32Signed Xlen ((cs1 @% "val") <<
                                                           (ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm inst)))]));
          instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
        |};
        {|instName := "SRLIW";
          uniqId := [fieldVal opcodeField (5'b"00110");
                     fieldVal funct3Field (3'b"101");
                     fieldVal funct7Field (7'b"0000000")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- (Trunc32Unsigned Xlen (cs1 @% "val")) >>>
                                       (ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm inst))]));
          instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
        |};
        {|instName := "SRAIW";
          uniqId := [fieldVal opcodeField (5'b"00110");
                     fieldVal funct3Field (3'b"101");
                     fieldVal funct7Field (7'b"0100000")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- (Trunc32Signed Xlen (cs1 @% "val")) >>>
                                       (ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm inst))]));
          instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
        |};
        {|instName := "AddW";
          uniqId := [fieldVal opcodeField (5'b"01110");
                     fieldVal funct3Field (3'b"000");
                     fieldVal funct7Field (7'b"0000000")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- Trunc32Signed Xlen ((cs1 @% "val") + (cs2 @% "val"))]));
          instProperties := {| hasCs1 := true; hasCs2 := true; implicit := 0 |}
        |};
        {|instName := "SubW";
          uniqId := [fieldVal opcodeField (5'b"01110");
                     fieldVal funct3Field (3'b"000");
                     fieldVal funct7Field (7'b"0100000")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- Trunc32Signed Xlen ((cs1 @% "val") - (cs2 @% "val"))]));
          instProperties := {| hasCs1 := true; hasCs2 := true; implicit := 0 |}
        |};
        {|instName := "SLLW";
          uniqId := [fieldVal opcodeField (5'b"01110");
                     fieldVal funct3Field (3'b"001");
                     fieldVal funct7Field (7'b"0000000")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- Trunc32Signed Xlen
                                       ((cs1 @% "val") <<
                                          (ZeroExtendTruncLsb (Nat.log2_up Xlen) (cs2 @% "val")))]));
          instProperties := {| hasCs1 := true; hasCs2 := true; implicit := 0 |}
        |};
        {|instName := "SRLW";
          uniqId := [fieldVal opcodeField (5'b"01110");
                     fieldVal funct3Field (3'b"101");
                     fieldVal funct7Field (7'b"0000000")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- (Trunc32Unsigned Xlen (cs1 @% "val")) >>>
                                       (ZeroExtendTruncLsb (Nat.log2_up Xlen) (cs2 @% "val"))]));
          instProperties := {| hasCs1 := true; hasCs2 := true; implicit := 0 |}
        |};
        {|instName := "SRAW";
          uniqId := [fieldVal opcodeField (5'b"01110");
                     fieldVal funct3Field (3'b"101");
                     fieldVal funct7Field (7'b"0100000")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- (Trunc32Signed Xlen (cs1 @% "val")) >>>
                                       (ZeroExtendTruncLsb (Nat.log2_up Xlen) (cs2 @% "val"))]));
          instProperties := {| hasCs1 := true; hasCs2 := true; implicit := 0 |}
        |}
      ]
    |}.

  Definition capInsts: InstEntryFull BaseOutput :=
    {|xlens := [32; 64];
      extension := Base;
      instEntries := [
        {|instName := "AUICGP";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"7b"))];
          inputXform ty pc inst cs1 cs2 ie :=
            ( LETC newAddr <- (cs1 @% "val") + SignExtendTruncLsb Xlen ({< auiLuiOffset inst, $$(wzero 11) >});
              LETE baseTop <- getCapBaseTop capAccessors (cs1 @% "cap") (cs1 @% "val");
              LETC baseBound <- #newAddr >= (#baseTop @% "base");
              LETC topBound <- (ZeroExtend 1 #newAddr) + $1 <= (#baseTop @% "top");
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdTag" <- (cs1 @% "tag") && !isSealed capAccessors (cs1 @% "cap") && (#baseBound && #topBound) ]
                      @%[ "cdCap" <- cs1 @% "cap" ]
                      @%[ "cdVal" <- #newAddr ]));
          instProperties := {| hasCs1 := false; hasCs2 := false; implicit := 3 |}
        |};
        {|instName := "AUIPCC";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"17"))];
          inputXform ty pc inst cs1 cs2 ie :=
            ( LETC newAddr <- (pc @% "val") + SignExtendTruncLsb Xlen ({< auiLuiOffset inst, $$(wzero 11) >});
              LETE baseTop <- getCapBaseTop capAccessors (pc @% "cap") (pc @% "val");
              LETC baseBound <- #newAddr >= (#baseTop @% "base");
              LETC topBound <- ZeroExtend 1 #newAddr + $1 <= #baseTop @% "top";
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdTag" <- #baseBound && #topBound ]
                      @%[ "cdCap" <- pc @% "cap" ]
                      @%[ "cdVal" <- #newAddr ]));
          instProperties := {| hasCs1 := false; hasCs2 := false; implicit := 3 |}
        |};
        {|instName := "CAndPerm";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal funct7Field (7'h"d")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( LETE perms <- getCapPerms capAccessors (cs1 @% "cap");
              LETC newPerms <- unpack CapPerms (ZeroExtendTruncLsb (size CapPerms)
                                                  ((ZeroExtendTruncLsb Xlen (pack #perms)) .& (cs2 @% "val")));
              LETE newCap <- setCapPerms capAccessors #newPerms (cs1 @% "cap");
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdTag" <- cs1 @% "tag" ]
                      @%[ "cdCap" <- #newCap ]
                      @%[ "cdVal" <- cs1 @% "val" ]));
          instProperties := {| hasCs1 := true; hasCs2 := true; implicit := 0 |}
        |};
        {|instName := "CClearTag";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal rs2FixedField (5'h"b");
                     fieldVal funct7Field (7'h"7f")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdTag" <- $$false ]
                      @%[ "cdCap" <- cs1 @% "cap" ]
                      @%[ "cdVal" <- cs1 @% "val" ]));
          instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
        |};
        {|instName := "CGetAddr";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal rs2FixedField (5'h"f");
                     fieldVal funct7Field (7'h"7f")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- cs1 @% "val" ]));
          instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
        |};
        {|instName := "CGetBase";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal rs2FixedField (5'h"2");
                     fieldVal funct7Field (7'h"7f")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( LETE baseTop <- getCapBaseTop capAccessors (cs1 @% "cap") (cs1 @% "val");
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- #baseTop @% "base" ]));
          instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
        |};
        {|instName := "CGetHigh";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal rs2FixedField (5'h"17");
                     fieldVal funct7Field (7'h"7f")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- cs1 @% "cap" ]));
          instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
        |};
        {|instName := "CGetLen";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal rs2FixedField (5'h"3");
                     fieldVal funct7Field (7'h"7f")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( LETE baseTop <- getCapBaseTop capAccessors (cs1 @% "cap") (cs1 @% "val");
              LETC len <- (#baseTop @% "top") - (ZeroExtend 1 (#baseTop @% "base"));
              LETC lenMsb <- unpack Bool (UniBit (TruncMsb Xlen 1) #len);
              LETC lenLsb <- UniBit (TruncLsb Xlen 1) #len;
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- ITE #lenMsb $$(wones Xlen) #lenLsb ]));
          instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
        |};
        {|instName := "CGetPerm";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal rs2FixedField (5'h"0");
                     fieldVal funct7Field (7'h"7f")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( LETE perms <- getCapPerms capAccessors (cs1 @% "cap");
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- ZeroExtendTruncLsb Xlen (pack #perms) ]));
          instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
        |};
        {|instName := "CGetTag";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal rs2FixedField (5'h"4");
                     fieldVal funct7Field (7'h"7f")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- ZeroExtendTruncLsb Xlen (pack (cs1 @% "tag")) ]));
          instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
        |};
        {|instName := "CGetTop";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal rs2FixedField (5'h"18");
                     fieldVal funct7Field (7'h"7f")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( LETE baseTop <- getCapBaseTop capAccessors (cs1 @% "cap") (cs1 @% "val");
              LETC topMsb <- unpack Bool (UniBit (TruncMsb Xlen 1) (#baseTop @% "top"));
              LETC topLsb <- UniBit (TruncLsb Xlen 1) (#baseTop @% "top");
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- ITE #topMsb $$(wones Xlen) #topLsb ]));
          instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
        |};
        {|instName := "CGetType";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal rs2FixedField (5'h"1");
                     fieldVal funct7Field (7'h"7f")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( LETC oType <- getCapOType capAccessors (cs1 @% "cap");
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- ZeroExtendTruncLsb Xlen #oType ]));
          instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
        |};
        {|instName := "CIncAddr";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal funct7Field (7'h"11")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( LETC newAddr <- (cs1 @% "val") + (cs2 @% "val");
              LETE baseTop <- getCapBaseTop capAccessors (cs1 @% "cap") (cs1 @% "val");
              LETC baseBound <- #newAddr >= #baseTop @% "base";
              LETC topBound <- ZeroExtend 1 #newAddr + $1 <= #baseTop @% "top";
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdTag" <- (cs1 @% "tag") && !isSealed capAccessors (cs1 @% "val") && (#baseBound && #topBound) ]
                      @%[ "cdCap" <- cs1 @% "cap" ]
                      @%[ "cdVal" <- #newAddr ]));
          instProperties := {| hasCs1 := true; hasCs2 := true; implicit := 0 |}
        |};
        {|instName := "CIncAddrImm";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"1")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( LETC newAddr <- (cs1 @% "val") + SignExtendTruncLsb Xlen (imm inst);
              LETE baseTop <- getCapBaseTop capAccessors (cs1 @% "cap") (cs1 @% "val");
              LETC baseBound <- #newAddr >= #baseTop @% "base";
              LETC topBound <- ZeroExtend 1 #newAddr + $1 <= #baseTop @% "top";
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdTag" <- (cs1 @% "tag") && !isSealed capAccessors (cs1 @% "val") && (#baseBound && #topBound) ]
                      @%[ "cdCap" <- cs1 @% "cap" ]
                      @%[ "cdVal" <- #newAddr ]));
          instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
        |};
        {|instName := "CMove";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal rs2FixedField (5'h"a");
                     fieldVal funct7Field (7'h"7f")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdTag" <- cs1 @% "tag" ]
                      @%[ "cdCap" <- cs1 @% "cap" ]
                      @%[ "cdVal" <- cs1 @% "val" ]));
          instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
        |};
        {|instName := "CRepresentableAlignmentMask";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal rs2FixedField (5'h"9");
                     fieldVal funct7Field (7'h"7f")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( LETE capBounds <- getCapBounds capAccessors ($0) (cs1 @% "val");
              LETC mask <- $$(wones Xlen) << (#capBounds @% "exp");
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- #mask ]));
          instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
        |};
        {|instName := "CRoundRepresentableLength";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal rs2FixedField (5'h"8");
                     fieldVal funct7Field (7'h"7f")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( LETE capBounds <- getCapBounds capAccessors ($0) (cs1 @% "val");
              LETC mask <- $$(wones Xlen) << (#capBounds @% "exp");
              LETC repLen <- (cs1 @% "val" + (~#mask)) .& #mask;
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- #repLen ]));
          instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
        |};
        {|instName := "CSetAddr";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal funct7Field (7'h"10")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( LETC newAddr <- cs2 @% "val";
              LETE baseTop <- getCapBaseTop capAccessors (cs1 @% "cap") (cs1 @% "val");
              LETC baseBound <- #newAddr >= (#baseTop @% "base");
              LETC topBound <- ZeroExtend 1 #newAddr + $1 <= (#baseTop @% "top");
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdTag" <- (cs1 @% "tag") && !isSealed capAccessors (cs1 @% "val") && (#baseBound && #topBound) ]
                      @%[ "cdCap" <- cs1 @% "cap" ]
                      @%[ "cdVal" <- #newAddr ]));
          instProperties := {| hasCs1 := true; hasCs2 := true; implicit := 0 |}
        |};
        {|instName := "CSetBounds";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal funct7Field (7'h"8")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( LETE baseTop <- getCapBaseTop capAccessors (cs1 @% "cap") (cs1 @% "val");
              LETC baseBound <- (cs1 @% "val") >= (#baseTop @% "base");
              LETC topBound <- (ZeroExtend 1 (cs1 @% "val") + ZeroExtend 1 (cs2 @% "val")) <= (#baseTop @% "top");
              LETE capBounds <- getCapBounds capAccessors (cs1 @% "cap") (cs1 @% "val");
              LETC newCap <- setCapBounds capAccessors (cs1 @% "cap") (#capBounds @% "B") (#capBounds @% "T") (#capBounds @% "exp");
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdTag" <- (cs1 @% "tag") && !isSealed capAccessors (cs1 @% "val") && (#baseBound && #topBound) ]
                      @%[ "cdCap" <- #newCap ]
                      @%[ "cdVal" <- cs1 @% "val" ]));
          instProperties := {| hasCs1 := true; hasCs2 := true; implicit := 0 |}
        |};
        {|instName := "CSetBoundsExact";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal funct7Field (7'h"9")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( LETE baseTop <- getCapBaseTop capAccessors (cs1 @% "cap") (cs1 @% "val");
              LETC baseBound <- (cs1 @% "val") >= (#baseTop @% "base");
              LETC topBound <- (ZeroExtend 1 (cs1 @% "val") + ZeroExtend 1 (cs2 @% "val")) <= (#baseTop @% "top");
              LETE capBounds <- getCapBounds capAccessors (cs1 @% "cap") (cs1 @% "val");
              LETC newCap <- setCapBounds capAccessors (cs1 @% "cap") (#capBounds @% "B") (#capBounds @% "T") (#capBounds @% "exp");
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdTag" <- (cs1 @% "tag") && !isSealed capAccessors (cs1 @% "val") && (#baseBound && #topBound) && (#capBounds @% "exact?")]
                      @%[ "cdCap" <- #newCap ]
                      @%[ "cdVal" <- cs1 @% "val" ]));
          instProperties := {| hasCs1 := true; hasCs2 := true; implicit := 0 |}
        |};
        {|instName := "CSetBoundsImm";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"2")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( LETE baseTop <- getCapBaseTop capAccessors (cs1 @% "cap") (cs1 @% "val");
              LETC baseBound <- (cs1 @% "val") >= (#baseTop @% "base");
              LETC topBound <- (ZeroExtend 1 (cs1 @% "val") + ZeroExtendTruncLsb (Xlen + 1) (imm inst)) <= (#baseTop @% "top");
              LETE capBounds <- getCapBounds capAccessors (cs1 @% "cap") (cs1 @% "val");
              LETC newCap <- setCapBounds capAccessors (cs1 @% "cap") (#capBounds @% "B") (#capBounds @% "T") (#capBounds @% "exp");
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdTag" <- (cs1 @% "tag") && !isSealed capAccessors (cs1 @% "val") && (#baseBound && #topBound) ]
                      @%[ "cdCap" <- #newCap ]
                      @%[ "cdVal" <- cs1 @% "val" ]));
          instProperties := {| hasCs1 := true; hasCs2 := true; implicit := 0 |}
        |};
        {|instName := "CSetEqualExact";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal funct7Field (7'h"21")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( LETC tagEq <- (cs1 @% "tag") == (cs2 @% "tag");
              LETC capEq <- (cs1 @% "cap") == (cs2 @% "cap");
              LETC valEq <- (cs1 @% "val") == (cs2 @% "val");
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- ZeroExtendTruncLsb Xlen (pack (#tagEq && #capEq && #valEq)) ]));
          instProperties := {| hasCs1 := true; hasCs2 := true; implicit := 0 |}
        |};
        {|instName := "CSetHigh";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal funct7Field (7'h"16")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdTag" <- $$false ]
                      @%[ "cdCap" <- cs2 @% "val" ]
                      @%[ "cdVal" <- cs1 @% "val" ]));
          instProperties := {| hasCs1 := true; hasCs2 := true; implicit := 0 |}
        |};
        {|instName := "CSub";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal funct7Field (7'h"14")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- (cs1 @% "val") - (cs2 @% "val") ]));
          instProperties := {| hasCs1 := true; hasCs2 := true; implicit := 0 |}
        |};
        {|instName := "CTestSubset";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal funct7Field (7'h"20")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( LETE baseTop <- getCapBaseTop capAccessors (cs1 @% "cap") (cs1 @% "val");
              LETE baseTop2 <- getCapBaseTop capAccessors (cs2 @% "cap") (cs2 @% "val");
              LETC baseBound <- (#baseTop2 @% "base") >= (#baseTop @% "base");
              LETC topBound <- (#baseTop2 @% "top") <= (#baseTop @% "top");
              LETC tagEq <- (cs1 @% "tag") == (cs2 @% "tag");
              LETE perms <- getCapPerms capAccessors (cs1 @% "cap");
              LETE perms2 <- getCapPerms capAccessors (cs2 @% "cap");
              LETC permsAnd <- (pack #perms .& pack #perms2);
              LETC permsSub <- #permsAnd == pack #perms2;
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- ZeroExtendTruncLsb Xlen (pack (#baseBound && #topBound && #tagEq && #permsSub)) ]));
          instProperties := {| hasCs1 := true; hasCs2 := true; implicit := 0 |}
        |};
        {|instName := "CSeal";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal funct7Field (7'h"b")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( LETE baseTop2 <- getCapBaseTop capAccessors (cs2 @% "cap") (cs2 @% "val");
              LETC baseBound <- (cs2 @% "val") >= (#baseTop2 @% "base");
              LETC topBound <- ZeroExtend 1 (cs2 @% "val") + $1 <= (#baseTop2 @% "top");
              LETE perms <- getCapPerms capAccessors (cs1 @% "cap");
              LETE perms2 <- getCapPerms capAccessors (cs2 @% "cap");
              LETC validSealAddr <- isSealAddr capAccessors (cs2 @% "val") (#perms @% "EX");
              LETC newCap <- seal capAccessors (ZeroExtendTruncLsb (CapOTypeSz capAccessors) (cs2 @% "val")) (cs1 @% "cap");
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdTag" <- (cs2 @% "tag") && !isSealed capAccessors (cs2 @% "cap") && (#baseBound && #topBound) &&
                                       (cs1 @% "tag") && !isSealed capAccessors (cs1 @% "cap") && (#perms2 @% "SE") && #validSealAddr]
                      @%[ "cdCap" <- #newCap ]
                      @%[ "cdVal" <- cs1 @% "val" ]));
          instProperties := {| hasCs1 := true; hasCs2 := true; implicit := 0 |}
        |};
        {|instName := "CUnseal";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal funct7Field (7'h"c")];
          inputXform ty pc inst cs1 cs2 ie :=
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
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdTag" <- (cs2 @% "tag") && !isSealed capAccessors (cs2 @% "cap") && (#baseBound && #topBound) &&
                                       (cs1 @% "tag") && isSealed capAccessors (cs1 @% "cap") && (#perms2 @% "US") && #oTypeEq]
                      @%[ "cdCap" <- #newCap ]
                      @%[ "cdVal" <- cs1 @% "val" ]));
          instProperties := {| hasCs1 := true; hasCs2 := true; implicit := 0 |}
        |}
      ]
    |}.

  Definition mkBranchInst (name: string) funct3Val (takenFn: forall {ty}, Data @# ty -> Data @# ty -> Bool ## ty) :=
      {|instName := name;
        uniqId := [fieldVal opcodeField (5'b"11000");
                   fieldVal funct3Field funct3Val];
        inputXform ty pc inst cs1 cs2 ie :=
          ( LETC newAddr <- (pc @% "val") + SignExtendTruncLsb Xlen (branchOffset inst);
            LETE taken <- takenFn (cs1 @% "val") (cs2 @% "val");
            RetE ((DefBaseOutput ty)
                    @%[ "mayChangePc?" <- $$true ]
                    @%[ "taken?" <- #taken ]
                    @%[ "pcMemAddr" <- #newAddr ]
                    @%[ "exception?" <- if compressed
                                        then $$false
                                        else isNotZero (ZeroExtendTruncLsb 2 #newAddr) ]
                    @%[ "exceptionCause" <- if compressed
                                            then Const ty (natToWord Xlen 0)
                                            else $InstMisaligned ]
                    @%[ "exceptionCausePc?" <- $$true ]));
        instProperties := {| hasCs1 := true; hasCs2 := true; implicit := 0 |}
      |}.

  Definition branchInsts: InstEntryFull BaseOutput :=
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

  Definition mkLdInst (name: string) funct3Val (size: nat) (isCap sign: bool) :=
    {|instName := name;
      uniqId := [fieldVal opcodeField (5'b"00000");
                 fieldVal funct3Field funct3Val];
      inputXform ty pc inst cs1 cs2 ie :=
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
          RetE ((DefBaseOutput ty)
                  @%[ "exception?" <- #fullException @% "valid" ]
                  @%[ "exceptionCause" <- #fullException @% "data" ]
                  @%[ "pcMemAddr" <- #newAddr ]
                  @%[ "memCap?" <- $$isCap ]
                  @%[ "memSize" <- Const ty (natToWord MemSizeSz size) ]
                  @%[ "mem?" <- $$true ]
                  @%[ "ldSigned?" <- $$sign ]
                  @%[ "ldPerms" <- #perms ]));
      instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
    |}.

  Definition ldInsts: InstEntryFull BaseOutput :=
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
  
  Definition ld32Insts: InstEntryFull BaseOutput :=
    {|xlens := [32];
      extension := Base;
      instEntries := [
        mkLdInst "CLC"  ('b"011") 8 true  false
      ]
    |}.
  
  Definition ld64Insts: InstEntryFull BaseOutput :=
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
      inputXform ty pc inst cs1 cs2 ie :=
        ( LETC newAddr <- (cs1 @% "val") + SignExtendTruncLsb Xlen (imm inst);
          LETE baseTop <- getCapBaseTop capAccessors (cs1 @% "cap") (cs1 @% "val");
          LETC baseBound <- #newAddr >= (#baseTop @% "base");
          LETC topBound <- ZeroExtend 1 #newAddr + $size <= (#baseTop @% "top");
          LETE perms <- getCapPerms capAccessors (cs1 @% "cap");
          LETE perms2 <- getCapPerms capAccessors (cs2 @% "cap");
          LETC fullException
            : Maybe Data <-
                (IF !(cs1 @% "tag")
                 then Valid (Const ty (natToWord Xlen CapTagViolation))
                 else (IF isSealed capAccessors (cs1 @% "cap")
                       then Valid (Const ty (natToWord Xlen CapSealViolation))
                       else (IF !(#perms @% "SD")
                             then Valid (Const ty (natToWord Xlen CapStViolation))
                             else (IF !(#perms @% "SL") && (cs2 @% "tag") && !(#perms2 @% "GL")
                                   then Valid (Const ty (natToWord Xlen CapStLocalViolation))
                                   else (IF !(#baseBound && #topBound)
                                         then Valid (Const ty (natToWord Xlen CapBoundsViolation))
                                         else StaticIf isCap
                                                (isNotZero (ZeroExtendTruncLsb (Nat.log2_up ((Xlen + CapSz)/8)) #newAddr))
                                                (Valid (Const ty (natToWord Xlen CapStMisaligned)))
                                                Invalid)))));
          RetE ((DefBaseOutput ty)
                  @%[ "exception?" <- #fullException @% "valid" ]
                  @%[ "exceptionCause" <- #fullException @% "data" ]
                  @%[ "pcMemAddr" <- #newAddr ]
                  @%[ "memCap?" <- $$isCap ]
                  @%[ "memSize" <- Const ty (natToWord MemSizeSz size) ]
                  @%[ "mem?" <- $$true ]
                  @%[ "store?" <- $$true ]
                  @%[ "cdTag" <- cs2 @% "tag"]
                  @%[ "cdCap" <- cs2 @% "cap"]
                  @%[ "cdVal" <- cs2 @% "val"] ));
      instProperties := {| hasCs1 := true; hasCs2 := true; implicit := 0 |}
    |}.

  Definition stInsts: InstEntryFull BaseOutput :=
    {|xlens := [32; 64];
      extension := Base;
      instEntries := [
        mkStInst "CSB"  ('b"000") 1 false;
        mkStInst "CSH"  ('b"001") 2 false;
        mkStInst "CSW"  ('b"010") 4 false
      ]
    |}.
  
  Definition st32Insts: InstEntryFull BaseOutput :=
    {|xlens := [32];
      extension := Base;
      instEntries := [
        mkStInst "CSC"  ('b"011") 8 true
      ]
    |}.
  
  Definition st64Insts: InstEntryFull BaseOutput :=
    {|xlens := [64];
      extension := Base;
      instEntries := [
      ]
    |}.

  Definition jumpInsts: InstEntryFull BaseOutput :=
    {|xlens := [32; 64];
      extension := Base;
      instEntries := [
        {|instName := "CJAL";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"6f"))];
          inputXform ty pc inst cs1 cs2 ie :=
            ( LETC newAddr <- (pc @% "val") + SignExtendTruncLsb Xlen (jalOffset inst);
              LETC linkAddr <- (pc @% "val") + ITE (isInstNotCompressed inst) $4 $2;
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdTag" <- $$true ]
                      @%[ "cdCap" <- seal capAccessors (getOTypeFromIe capAccessors ie) (pc @% "cap") ]
                      @%[ "cdVal" <- #linkAddr ]
                      @%[ "mayChangePc?" <- $$true ]
                      @%[ "taken?" <- $$true ]
                      @%[ "pcMemAddr" <- #newAddr ]
                      @%[ "exception?" <- if compressed
                                          then $$false
                                          else isNotZero (ZeroExtendTruncLsb 2 #newAddr) ]
                      @%[ "exceptionCause" <- if compressed
                                              then Const ty (natToWord Xlen 0)
                                              else $InstMisaligned ]
                      @%[ "exceptionCausePc?" <- $$true ]));
          instProperties := {| hasCs1 := false; hasCs2 := false; implicit := 0 |}
        |};
        {|instName := "CJALR";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"67"));
                     fieldVal funct3Field (3'h"0")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( LETC newAddrTemp <- (cs1 @% "val") + SignExtendTruncLsb Xlen (imm inst);
              LETC newAddr <- ZeroExtendTruncLsb Xlen ({< ZeroExtendTruncMsb (Xlen - 1) #newAddrTemp, $$WO~0 >});
              LETC linkAddr <- (pc @% "val") + ITE (isInstNotCompressed inst) $4 $2;
              LETE perms <- getCapPerms capAccessors (cs1 @% "cap");
              LETC fullException
                : Pair (Maybe Data) Bool <-
                    (IF !(cs1 @% "tag")
                     then mkPair (Valid (Const ty (natToWord Xlen CapTagViolation))) ($$false)
                     else (IF isSealed capAccessors (cs1 @% "cap") &&
                             (!isSentry capAccessors (cs1 @% "cap") || isNotZero (imm inst) )
                           then mkPair (Valid (Const ty (natToWord Xlen CapSealViolation))) ($$false)
                           else (IF !(#perms @% "EX")
                                 then mkPair (Valid (Const ty (natToWord Xlen CapExecViolation))) ($$false)
                                 else if compressed
                                      then mkPair Invalid ($$false)
                                      else mkPair (Valid (Const ty (natToWord Xlen InstMisaligned))) ($$true))));
              LETC ieSentry <- isIeSentry capAccessors (cs1 @% "cap");
              LETC idSentry <- isIdSentry capAccessors (cs1 @% "cap");
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdTag" <- $$true ]
                      @%[ "cdCap" <- seal capAccessors (getOTypeFromIe capAccessors ie) (pc @% "cap") ]
                      @%[ "cdVal" <- #linkAddr ]
                      @%[ "mayChangePc?" <- $$true ]
                      @%[ "taken?" <- $$true ]
                      @%[ "pcMemAddr" <- #newAddr ]
                      @%[ "changePcCap?" <- $$true ]
                      @%[ "pcCap" <- unseal capAccessors (cs1 @% "cap") ]
                      @%[ "exception?" <- #fullException @% "fst" @% "valid" ]
                      @%[ "exceptionCause" <- #fullException @% "fst" @% "data" ]
                      @%[ "exceptionCausePc?" <- #fullException @% "snd" ]
                      @%[ "changeIe?" <- #ieSentry || #idSentry ]
                      @%[ "newIe" <- #ieSentry ] ));
          instProperties := {| hasCs1 := true; hasCs2 := false; implicit := 0 |}
        |}
      ]
    |}.

  Definition interruptInsts: InstEntryFull BaseOutput :=
    {|xlens := [32; 64];
      extension := Base;
      instEntries := [
        {|instName := "FenceI";
          uniqId := [fieldVal opcodeField (5'b"00011");
                     fieldVal funct3Field (3'b"001")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "interrupt?" <- $$true ]
                      @%[ "exceptionCause" <- Const ty (natToWord Xlen FenceI) ]));
          instProperties := {| hasCs1 := false; hasCs2 := false; implicit := 0 |}
        |};
        {|instName := "WFI";
          uniqId := [fieldVal opcodeField (5'b"11100");
                     fieldVal rdFixedField (5'b"00000");
                     fieldVal funct3Field (3'b"000");
                     fieldVal rs1FixedField (5'b"00000");
                     fieldVal rs2FixedField (5'b"00101");
                     fieldVal funct7Field (7'b"0001000")];
          inputXform ty pc inst cs1 cs2 ie :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "interrupt?" <- $$true ]
                      @%[ "exceptionCause" <- Const ty (natToWord Xlen WFI) ]));
          instProperties := {| hasCs1 := false; hasCs2 := false; implicit := 0 |}
        |}
      ]
    |}.

  Definition specBaseFuncUnit : FuncEntry :=
    {|localFuncInput := BaseOutput;
      localFuncOutput := BaseOutput;
      localFunc ty x := RetE x;
      outputXform := baseOutputXform;
      insts := [aluInsts; alu64Insts; capInsts; branchInsts; ldInsts; ld32Insts; ld64Insts; stInsts; st32Insts; st64Insts; jumpInsts; interruptInsts]
    |}.

  Definition specBaseInsts : list (InstEntry BaseOutput) := filtInsts (mkFiltFuncEntry specBaseFuncUnit).

  Ltac simplify_field field :=
    repeat match goal with
           | |- context [field ?P] =>
               let sth := fresh "sth" in
               let Heq_sth := fresh "Heq_sth" in
               remember (field P) as sth eqn: Heq_sth; simpl in Heq_sth; rewrite Heq_sth; clear Heq_sth sth
           end.

  Theorem uniqAluIds: NoDup (map (@uniqId _ BaseOutput) specBaseInsts).
  Proof.
    unfold specBaseInsts, mkFiltFuncEntry, filtInsts, specBaseFuncUnit, insts, localFuncInput, localFuncOutput, fold_left.
    pose proof extsHasBase as base.
    simplify_field (@extension procParams BaseOutput).
    destruct (in_dec Extension_eq_dec Base supportedExts); [| unfold getBool; rewrite ?andb_false_r; simpl; auto; constructor].
    simplify_field (@xlens procParams BaseOutput).
    destruct (xlenIs32_or_64) as [H | H]; do 2 (rewrite H; simpl);
      repeat constructor; unfold In, not; intros;
      repeat match goal with
        | H: ?p \/ ?q |- _ => destruct H; try discriminate
        end; auto.
  Qed.

End InstBaseSpec.
