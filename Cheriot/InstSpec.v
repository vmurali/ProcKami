Require Import Kami.AllNotations ProcKami.Cheriot.Lib ProcKami.Cheriot.Types ProcKami.Cheriot.DecExec.
Require Import RecordUpdate.RecordUpdate.

Section InstBaseSpec.
  Context `{procParams: ProcParams}.
  Local Open Scope kami_expr.

  Definition BaseOutput :=
    STRUCT_TYPE {
        "wb?" :: Bool;
        "cdTag" :: Bool;
        "cdCap" :: Cap;
        "cdVal" :: Data;
        "taken?" :: Bool;
        "pcMemAddr" :: Addr;
        "changePcCap?" :: Bool;
        "pcCap" :: Cap;
        "changeIe?" :: Bool;
        "newIe" :: Bool;
        "exception?" :: Bool;
        "exceptionCause" :: Data;
        "exceptionValue" :: Addr;
        "baseException?" :: Bool;
        "pcCapException?" :: Bool;
        "mem?" :: Bool;
        "memCap?" :: Bool;
        "memSize" :: MemSize;
        "store?" :: Bool;
        "ldSigned?" :: Bool;
        "ldPerms" :: CapPerms;
        "fenceI?" :: Bool;
        "wbScr?" :: Bool;
        "scrTag" :: Bool;
        "scrCap" :: Cap;
        "scrVal" :: Data;
        "scrException?" :: Bool;
        "wbCsr?" :: Bool;
        "csrVal" :: Data }.

  Section ty.
    Variable ty: Kind -> Type.
    Local Definition Trunc32Signed := @TruncToSizeSigned ty 32.
    Local Definition Trunc32Unsigned := @TruncToSizeUnsigned ty 32.
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
                        "cap" ::= ITE (inp @% "exception?") (inp @% "exceptionValue") (inp @% "cdCap");
                        "val" ::= (IF (inp @% "exception?")
                                   then inp @% "exceptionCause"
                                   else inp @% "cdVal") };
        RetE (STRUCT {
                  "data" ::= #cd;
                  "pcOrScrCapOrMemOp" ::= (IF (inp @% "mem?")
                                           then ZeroExtendTruncLsb CapSz (pack #memOp)
                                           else (IF (inp @% "wbScr?")
                                                 then inp @% "scrCap"
                                                 else inp @% "pcCap"));
                  "addrOrScrOrCsrVal" ::= (IF (inp @% "wbScr?")
                                           then inp @% "scrVal"
                                           else (IF (inp @% "wbCsr?")
                                                 then inp @% "csrVal"
                                                 else inp @% "pcMemAddr"));
                  "wb?" ::= inp @% "wb?";
                  "taken?" ::= inp @% "taken?";
                  "changePcCap?" ::= inp @% "changePcCap?";
                  "mem?" ::= inp @% "mem?";
                  "exception?" ::= inp @% "exception?";
                  "baseException?" ::= inp @% "baseException?";
                  "pcCapException?" ::= inp @% "pcCapException?";
                  "fenceI?" ::= inp @% "fenceI?";
                  "changeIe?" ::= inp @% "changeIe?";
                  "newIe" ::= inp @% "newIe";
                  "wbScr?" ::= inp @% "wbScr?";
                  "scrTag" ::= inp @% "scrTag";
                  "scrException?" ::= inp @% "scrException?";
                  "wbCsr?" ::= inp @% "wbCsr?" } : FuncOutput @# ty) ).
  End ty.

  Definition aluInsts: InstEntryFull BaseOutput :=
    {|xlens := [32; 64];
      extension := Base;
      instEntries := [
        {|instName := "AddI";
          uniqId := [fieldVal opcodeField (5'b"00100");
                     fieldVal funct3Field (3'b"000")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- (cs1 @% "val") + SignExtendTruncLsb Xlen (imm inst)]));
          instProperties := DefProperties<| hasCs1 := true |>
        |};
        {|instName := "SLTI";
          uniqId := [fieldVal opcodeField (5'b"00100");
                     fieldVal funct3Field (3'b"010")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( LETC in1 <- SignExtend 1 (cs1 @% "val");
              LETC in2 <- SignExtendTruncLsb (Xlen + 1) (imm inst);
              LETC res <- #in1 - #in2;
              LETC msb <- UniBit (TruncMsb Xlen 1) #res;
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- ZeroExtendTruncLsb Xlen #msb]));
          instProperties := DefProperties<| hasCs1 := true |>
        |};
        {|instName := "SLTIU";
          uniqId := [fieldVal opcodeField (5'b"00100");
                     fieldVal funct3Field (3'b"011")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( LETC in1 <- ZeroExtend 1 (cs1 @% "val");
              LETC in2 <- ZeroExtendTruncLsb (Xlen + 1) (imm inst);
              LETC res <- #in1 - #in2;
              LETC msb <- UniBit (TruncMsb Xlen 1) #res;
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- ZeroExtendTruncLsb Xlen #msb]));
          instProperties := DefProperties<| hasCs1 := true |>
        |};
        {|instName := "XorI";
          uniqId := [fieldVal opcodeField (5'b"00100");
                     fieldVal funct3Field (3'b"100")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- ((cs1 @% "val") .^ (SignExtendTruncLsb Xlen (imm inst))) ]));
          instProperties := DefProperties<| hasCs1 := true |>
        |};
        {|instName := "OrI";
          uniqId := [fieldVal opcodeField (5'b"00100");
                     fieldVal funct3Field (3'b"110")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- ((cs1 @% "val") .| (SignExtendTruncLsb Xlen (imm inst))) ]));
          instProperties := DefProperties<| hasCs1 := true |>
        |};
        {|instName := "AndI";
          uniqId := [fieldVal opcodeField (5'b"00100");
                     fieldVal funct3Field (3'b"111")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- ((cs1 @% "val") .& (SignExtendTruncLsb Xlen (imm inst))) ]));
          instProperties := DefProperties<| hasCs1 := true |>
        |};
        {|instName := "SLLI";
          uniqId := [fieldVal opcodeField (5'b"00100");
                     fieldVal funct3Field (3'b"001");
                     if Xlen =? 32
                     then fieldVal funct7Field (7'b"0000000")
                     else fieldVal funct6Field (6'b"000000")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- ((cs1 @% "val") <<
                                        (ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm inst)))]));
          instProperties := DefProperties<| hasCs1 := true |>
        |};
        {|instName := "SRLI";
          uniqId := [fieldVal opcodeField (5'b"00100");
                     fieldVal funct3Field (3'b"101");
                     if Xlen =? 32
                     then fieldVal funct7Field (7'b"0000000")
                     else fieldVal funct6Field (6'b"000000")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- UniBit (TruncLsb Xlen 1)
                                       ((ZeroExtend 1 (cs1 @% "val")) >>>
                                          (ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm inst)))]));
          instProperties := DefProperties<| hasCs1 := true |>
        |};
        {|instName := "SRAI";
          uniqId := [fieldVal opcodeField (5'b"00100");
                     fieldVal funct3Field (3'b"101");
                     if Xlen =? 32
                     then fieldVal funct7Field (7'b"0100000")
                     else fieldVal funct6Field (6'b"010000")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- UniBit (TruncLsb Xlen 1)
                                       ((SignExtend 1 (cs1 @% "val")) >>>
                                          (ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm inst)))]));
          instProperties := DefProperties<| hasCs1 := true |>
        |};
        {|instName := "Add";
          uniqId := [fieldVal opcodeField (5'b"01100");
                     fieldVal funct3Field (3'b"000");
                     fieldVal funct7Field (7'b"0000000")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- (cs1 @% "val") + (cs2 @% "val")]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>
        |};
        {|instName := "Sub";
          uniqId := [fieldVal opcodeField (5'b"01100");
                     fieldVal funct3Field (3'b"000");
                     fieldVal funct7Field (7'b"0100000")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- (cs1 @% "val") - (cs2 @% "val")]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>
        |};
        {|instName := "SLT";
          uniqId := [fieldVal opcodeField (5'b"01100");
                     fieldVal funct3Field (3'b"010");
                     fieldVal funct7Field (7'b"0000000")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( LETC in1 <- SignExtend 1 (cs1 @% "val");
              LETC in2 <- SignExtend 1 (cs2 @% "val");
              LETC res <- UniBit (TruncMsb Xlen 1) (#in1 - #in2);
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- ZeroExtendTruncLsb Xlen #res]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>
        |};
        {|instName := "SLTU";
          uniqId := [fieldVal opcodeField (5'b"01100");
                     fieldVal funct3Field (3'b"011");
                     fieldVal funct7Field (7'b"0000000")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( LETC in1 <- ZeroExtend 1 (cs1 @% "val");
              LETC in2 <- ZeroExtend 1 (cs2 @% "val");
              LETC res <- UniBit (TruncMsb Xlen 1) (#in1 - #in2);
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- ZeroExtendTruncLsb Xlen #res]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>
        |};
        {|instName := "Xor";
          uniqId := [fieldVal opcodeField (5'b"01100");
                     fieldVal funct3Field (3'b"100");
                     fieldVal funct7Field (7'b"0000000")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- (cs1 @% "val") .^ (cs2 @% "val")]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>
        |};
        {|instName := "Or";
          uniqId := [fieldVal opcodeField (5'b"01100");
                     fieldVal funct3Field (3'b"110");
                     fieldVal funct7Field (7'b"0000000")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- (cs1 @% "val") .| (cs2 @% "val")]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>
        |};
        {|instName := "And";
          uniqId := [fieldVal opcodeField (5'b"01100");
                     fieldVal funct3Field (3'b"111");
                     fieldVal funct7Field (7'b"0000000")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- (cs1 @% "val") .& (cs2 @% "val")]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>
        |};
        {|instName := "SLL";
          uniqId := [fieldVal opcodeField (5'b"01100");
                     fieldVal funct3Field (3'b"001");
                     fieldVal funct7Field (7'b"0000000")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- (cs1 @% "val") <<
                                       (ZeroExtendTruncLsb (Nat.log2_up Xlen) (cs2 @% "val"))]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>
        |};
        {|instName := "SRL";
          uniqId := [fieldVal opcodeField (5'b"01100");
                     fieldVal funct3Field (3'b"101");
                     fieldVal funct7Field (7'b"0000000")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- UniBit (TruncLsb Xlen 1)
                                       ((ZeroExtend 1 (cs1 @% "val")) >>>
                                          (ZeroExtendTruncLsb (Nat.log2_up Xlen) (cs2 @% "val")))]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>
        |};
        {|instName := "SRA";
          uniqId := [fieldVal opcodeField (5'b"01100");
                     fieldVal funct3Field (3'b"101");
                     fieldVal funct7Field (7'b"0100000")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- UniBit (TruncLsb Xlen 1)
                                       ((SignExtend 1 (cs1 @% "val")) >>>
                                          (ZeroExtendTruncLsb (Nat.log2_up Xlen) (cs2 @% "val")))]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>
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
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- Trunc32Signed Xlen ((cs1 @% "val") + SignExtendTruncLsb Xlen (imm inst))]));
          instProperties := DefProperties<| hasCs1 := true |>
        |};
        {|instName := "SLLIW";
          uniqId := [fieldVal opcodeField (5'b"00110");
                     fieldVal funct3Field (3'b"001");
                     fieldVal funct7Field (7'b"0000000")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- Trunc32Signed Xlen ((cs1 @% "val") <<
                                                           (ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm inst)))]));
          instProperties := DefProperties<| hasCs1 := true |>
        |};
        {|instName := "SRLIW";
          uniqId := [fieldVal opcodeField (5'b"00110");
                     fieldVal funct3Field (3'b"101");
                     fieldVal funct7Field (7'b"0000000")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- (Trunc32Unsigned Xlen (cs1 @% "val")) >>>
                                       (ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm inst))]));
          instProperties := DefProperties<| hasCs1 := true |>
        |};
        {|instName := "SRAIW";
          uniqId := [fieldVal opcodeField (5'b"00110");
                     fieldVal funct3Field (3'b"101");
                     fieldVal funct7Field (7'b"0100000")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- (Trunc32Signed Xlen (cs1 @% "val")) >>>
                                       (ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm inst))]));
          instProperties := DefProperties<| hasCs1 := true |>
        |};
        {|instName := "AddW";
          uniqId := [fieldVal opcodeField (5'b"01110");
                     fieldVal funct3Field (3'b"000");
                     fieldVal funct7Field (7'b"0000000")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- Trunc32Signed Xlen ((cs1 @% "val") + (cs2 @% "val"))]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>
        |};
        {|instName := "SubW";
          uniqId := [fieldVal opcodeField (5'b"01110");
                     fieldVal funct3Field (3'b"000");
                     fieldVal funct7Field (7'b"0100000")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- Trunc32Signed Xlen ((cs1 @% "val") - (cs2 @% "val"))]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>
        |};
        {|instName := "SLLW";
          uniqId := [fieldVal opcodeField (5'b"01110");
                     fieldVal funct3Field (3'b"001");
                     fieldVal funct7Field (7'b"0000000")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- Trunc32Signed Xlen
                                       ((cs1 @% "val") <<
                                          (ZeroExtendTruncLsb (Nat.log2_up Xlen) (cs2 @% "val")))]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>
        |};
        {|instName := "SRLW";
          uniqId := [fieldVal opcodeField (5'b"01110");
                     fieldVal funct3Field (3'b"101");
                     fieldVal funct7Field (7'b"0000000")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- (Trunc32Unsigned Xlen (cs1 @% "val")) >>>
                                       (ZeroExtendTruncLsb (Nat.log2_up Xlen) (cs2 @% "val"))]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>
        |};
        {|instName := "SRAW";
          uniqId := [fieldVal opcodeField (5'b"01110");
                     fieldVal funct3Field (3'b"101");
                     fieldVal funct7Field (7'b"0100000")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- (Trunc32Signed Xlen (cs1 @% "val")) >>>
                                       (ZeroExtendTruncLsb (Nat.log2_up Xlen) (cs2 @% "val"))]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>
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

  Definition capInsts: InstEntryFull BaseOutput :=
    {|xlens := [32; 64];
      extension := Base;
      instEntries := [
        {|instName := "AUICGP";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"7b"))];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( LETC newAddr <- (cs1 @% "val") + SignExtendTruncLsb Xlen ({< auiLuiOffset inst, $$(wzero 11) >});
              LETE representable <- representableFn (justFullCap cs1) #newAddr;
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdTag" <- (cs1 @% "tag") && !isSealed capAccessors (cs1 @% "cap") && #representable ]
                      @%[ "cdCap" <- cs1 @% "cap" ]
                      @%[ "cdVal" <- #newAddr ]));
          instProperties := DefProperties<| implicit := 3 |>
        |};
        {|instName := "AUIPCC";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"17"))];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( LETC newAddr <- (pc @% "val") + SignExtendTruncLsb Xlen ({< auiLuiOffset inst, $$(wzero 11) >});
              LETE representable <- representableFn pc #newAddr;
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdTag" <- #representable ]
                      @%[ "cdCap" <- pc @% "cap" ]
                      @%[ "cdVal" <- #newAddr ]));
          instProperties := DefProperties
        |};
        {|instName := "CAndPerm";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal funct7Field (7'h"d")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( LETE perms <- getCapPerms capAccessors (cs1 @% "cap");
              LETC newPerms <- unpack CapPerms (ZeroExtendTruncLsb (size CapPerms)
                                                  ((ZeroExtendTruncLsb Xlen (pack #perms)) .& (cs2 @% "val")));
              LETE newCap <- setCapPerms capAccessors #newPerms (cs1 @% "cap");
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdTag" <- cs1 @% "tag" ]
                      @%[ "cdCap" <- #newCap ]
                      @%[ "cdVal" <- cs1 @% "val" ]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>
        |};
        {|instName := "CClearTag";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal rs2FixedField (5'h"b");
                     fieldVal funct7Field (7'h"7f")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdTag" <- $$false ]
                      @%[ "cdCap" <- cs1 @% "cap" ]
                      @%[ "cdVal" <- cs1 @% "val" ]));
          instProperties := DefProperties<| hasCs1 := true |>
        |};
        {|instName := "CGetAddr";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal rs2FixedField (5'h"f");
                     fieldVal funct7Field (7'h"7f")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- cs1 @% "val" ]));
          instProperties := DefProperties<| hasCs1 := true |>
        |};
        {|instName := "CGetBase";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal rs2FixedField (5'h"2");
                     fieldVal funct7Field (7'h"7f")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( LETE baseTop <- getCapBaseTop capAccessors (cs1 @% "cap") (cs1 @% "val");
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- #baseTop @% "base" ]));
          instProperties := DefProperties<| hasCs1 := true |>
        |};
        {|instName := "CGetHigh";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal rs2FixedField (5'h"17");
                     fieldVal funct7Field (7'h"7f")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- cs1 @% "cap" ]));
          instProperties := DefProperties<| hasCs1 := true |>
        |};
        {|instName := "CGetLen";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal rs2FixedField (5'h"3");
                     fieldVal funct7Field (7'h"7f")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( LETE baseTop <- getCapBaseTop capAccessors (cs1 @% "cap") (cs1 @% "val");
              LETC len <- (#baseTop @% "top") - (ZeroExtend 1 (#baseTop @% "base"));
              LETC lenMsb <- unpack Bool (UniBit (TruncMsb Xlen 1) #len);
              LETC lenLsb <- UniBit (TruncLsb Xlen 1) #len;
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- ITE #lenMsb $$(wones Xlen) #lenLsb ]));
          instProperties := DefProperties<| hasCs1 := true |>
        |};
        {|instName := "CGetPerm";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal rs2FixedField (5'h"0");
                     fieldVal funct7Field (7'h"7f")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( LETE perms <- getCapPerms capAccessors (cs1 @% "cap");
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- ZeroExtendTruncLsb Xlen (pack #perms) ]));
          instProperties := DefProperties<| hasCs1 := true |>
        |};
        {|instName := "CGetTag";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal rs2FixedField (5'h"4");
                     fieldVal funct7Field (7'h"7f")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- ZeroExtendTruncLsb Xlen (pack (cs1 @% "tag")) ]));
          instProperties := DefProperties<| hasCs1 := true |>
        |};
        {|instName := "CGetTop";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal rs2FixedField (5'h"18");
                     fieldVal funct7Field (7'h"7f")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( LETE baseTop <- getCapBaseTop capAccessors (cs1 @% "cap") (cs1 @% "val");
              LETC topMsb <- unpack Bool (UniBit (TruncMsb Xlen 1) (#baseTop @% "top"));
              LETC topLsb <- UniBit (TruncLsb Xlen 1) (#baseTop @% "top");
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- ITE #topMsb $$(wones Xlen) #topLsb ]));
          instProperties := DefProperties<| hasCs1 := true |>
        |};
        {|instName := "CGetType";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal rs2FixedField (5'h"1");
                     fieldVal funct7Field (7'h"7f")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( LETC oType <- getCapOType capAccessors (cs1 @% "cap");
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- ZeroExtendTruncLsb Xlen #oType ]));
          instProperties := DefProperties<| hasCs1 := true |>
        |};
        {|instName := "CIncAddr";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal funct7Field (7'h"11")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( LETC newAddr <- (cs1 @% "val") + (cs2 @% "val");
              LETE representable <- representableFn (justFullCap cs1) #newAddr;
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdTag" <- (cs1 @% "tag") && !isSealed capAccessors (cs1 @% "val") && #representable ]
                      @%[ "cdCap" <- cs1 @% "cap" ]
                      @%[ "cdVal" <- #newAddr ]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>
        |};
        {|instName := "CIncAddrImm";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"1")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( LETC newAddr <- (cs1 @% "val") + SignExtendTruncLsb Xlen (imm inst);
              LETE representable <- representableFn (justFullCap cs1) #newAddr;
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdTag" <- (cs1 @% "tag") && !isSealed capAccessors (cs1 @% "val") && #representable ]
                      @%[ "cdCap" <- cs1 @% "cap" ]
                      @%[ "cdVal" <- #newAddr ]));
          instProperties := DefProperties<| hasCs1 := true |>
        |};
        {|instName := "CMove";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal rs2FixedField (5'h"a");
                     fieldVal funct7Field (7'h"7f")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdTag" <- cs1 @% "tag" ]
                      @%[ "cdCap" <- cs1 @% "cap" ]
                      @%[ "cdVal" <- cs1 @% "val" ]));
          instProperties := DefProperties<| hasCs1 := true |>
        |};
        {|instName := "CRepresentableAlignmentMask";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal rs2FixedField (5'h"9");
                     fieldVal funct7Field (7'h"7f")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( LETE capBounds <- getCapBounds capAccessors ($0) (cs1 @% "val");
              LETC mask <- $$(wones Xlen) << (#capBounds @% "exp");
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- #mask ]));
          instProperties := DefProperties<| hasCs1 := true |>
        |};
        {|instName := "CRoundRepresentableLength";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal rs2FixedField (5'h"8");
                     fieldVal funct7Field (7'h"7f")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( LETE capBounds <- getCapBounds capAccessors ($0) (cs1 @% "val");
              LETC mask <- $$(wones Xlen) << (#capBounds @% "exp");
              LETC repLen <- (cs1 @% "val" + (~#mask)) .& #mask;
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- #repLen ]));
          instProperties := DefProperties<| hasCs1 := true |>
        |};
        {|instName := "CSetAddr";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal funct7Field (7'h"10")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( LETC newAddr <- cs2 @% "val";
              LETE representable <- representableFn (justFullCap cs1) #newAddr;
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdTag" <- (cs1 @% "tag") && !isSealed capAccessors (cs1 @% "val") && #representable ]
                      @%[ "cdCap" <- cs1 @% "cap" ]
                      @%[ "cdVal" <- #newAddr ]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>
        |};
        {|instName := "CSetBounds";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal funct7Field (7'h"8")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( LETE newCd <- setBounds cs1 (cs2 @% "val") $$false;
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdTag" <- #newCd @% "tag" ]
                      @%[ "cdCap" <- #newCd @% "cap" ]
                      @%[ "cdVal" <- #newCd @% "val" ]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>
        |};
        {|instName := "CSetBoundsExact";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal funct7Field (7'h"9")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( LETE newCd <- setBounds cs1 (cs2 @% "val") $$true;
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdTag" <- #newCd @% "tag" ]
                      @%[ "cdCap" <- #newCd @% "cap" ]
                      @%[ "cdVal" <- #newCd @% "val" ]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>
        |};
        {|instName := "CSetBoundsImm";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"2")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( LETE newCd <- setBounds cs1 (ZeroExtendTruncLsb Xlen (imm inst)) $$false;
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdTag" <- #newCd @% "tag" ]
                      @%[ "cdCap" <- #newCd @% "cap" ]
                      @%[ "cdVal" <- #newCd @% "val" ]));
          instProperties := DefProperties<| hasCs1 := true |>
        |};
        {|instName := "CSetEqualExact";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal funct7Field (7'h"21")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( LETC tagEq <- (cs1 @% "tag") == (cs2 @% "tag");
              LETC capEq <- (cs1 @% "cap") == (cs2 @% "cap");
              LETC valEq <- (cs1 @% "val") == (cs2 @% "val");
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- ZeroExtendTruncLsb Xlen (pack (#tagEq && #capEq && #valEq)) ]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>
        |};
        {|instName := "CSetHigh";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal funct7Field (7'h"16")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdTag" <- $$false ]
                      @%[ "cdCap" <- cs2 @% "val" ]
                      @%[ "cdVal" <- cs1 @% "val" ]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>
        |};
        {|instName := "CSub";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal funct7Field (7'h"14")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- (cs1 @% "val") - (cs2 @% "val") ]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>
        |};
        {|instName := "CTestSubset";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal funct7Field (7'h"20")];
          inputXform ty pc inst cs1 cs2 scr csr :=
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
                      @%[ "cdVal" <-
                            ZeroExtendTruncLsb Xlen (pack (#baseBound && #topBound && #tagEq && #permsSub)) ]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>
        |};
        {|instName := "CSeal";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal funct7Field (7'h"b")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( LETE baseTop2 <- getCapBaseTop capAccessors (cs2 @% "cap") (cs2 @% "val");
              LETC baseBound <- (cs2 @% "val") >= (#baseTop2 @% "base");
              LETC topBound <- ZeroExtend 1 (cs2 @% "val") + $1 <= (#baseTop2 @% "top");
              LETE perms <- getCapPerms capAccessors (cs1 @% "cap");
              LETE perms2 <- getCapPerms capAccessors (cs2 @% "cap");
              LETC validSealAddr <- isSealAddr capAccessors (cs2 @% "val") (#perms @% "EX");
              LETC newCap <- seal capAccessors
                               (ZeroExtendTruncLsb (CapOTypeSz capAccessors) (cs2 @% "val")) (cs1 @% "cap");
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdTag" <- (cs2 @% "tag") && !isSealed capAccessors (cs2 @% "cap") &&
                                       (#baseBound && #topBound) && (cs1 @% "tag") &&
                                       !isSealed capAccessors (cs1 @% "cap") && (#perms2 @% "SE") && #validSealAddr]
                      @%[ "cdCap" <- #newCap ]
                      @%[ "cdVal" <- cs1 @% "val" ]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>
        |};
        {|instName := "CUnseal";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"5b"));
                     fieldVal funct3Field (3'h"0");
                     fieldVal funct7Field (7'h"c")];
          inputXform ty pc inst cs1 cs2 scr csr :=
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
                      @%[ "cdTag" <- (cs2 @% "tag") && !isSealed capAccessors (cs2 @% "cap") &&
                                       (#baseBound && #topBound) && (cs1 @% "tag") &&
                                       isSealed capAccessors (cs1 @% "cap") && (#perms2 @% "US") && #oTypeEq]
                      @%[ "cdCap" <- #newCap ]
                      @%[ "cdVal" <- cs1 @% "val" ]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>
        |}
      ]
    |}.

  Definition mkBranchInst (name: string) funct3Val (takenFn: forall {ty}, Data @# ty -> Data @# ty -> Bool ## ty) :=
      {|instName := name;
        uniqId := [fieldVal opcodeField (5'b"11000");
                   fieldVal funct3Field funct3Val];
        inputXform ty pc inst cs1 cs2 scr csr :=
          ( LETC newAddr <- (pc @% "val") + SignExtendTruncLsb Xlen (branchOffset inst);
            LETE taken <- takenFn (cs1 @% "val") (cs2 @% "val");
            RetE ((DefBaseOutput ty)
                    @%[ "taken?" <- #taken ]
                    @%[ "pcMemAddr" <- #newAddr ]
                    @%[ "exception?" <- if compressed
                                        then $$false
                                        else isNotZero (ZeroExtendTruncLsb 2 #newAddr) ]
                    @%[ "exceptionCause" <- if compressed
                                            then $0
                                            else Const ty (natToWord Xlen InstMisaligned) ]
                    @%[ "exceptionValue" <- #newAddr ]
                    @%[ "baseException?" <- $$true ]));
        instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>
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

  Definition isBranchInsts ty (inst: Inst @# ty) :=
    redLet (@Kor _ _) (fun x => RetE (matchUniqId inst (uniqId x))) (filterInsts [branchInsts]).

  Definition mkLdInst (name: string) funct3Val (size: nat) (isCap sign: bool) :=
    {|instName := name;
      uniqId := [fieldVal opcodeField (5'b"00000");
                 fieldVal funct3Field funct3Val];
      inputXform ty pc inst cs1 cs2 scr csr :=
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
                  @%[ "wb?" <- $$true ]
                  @%[ "exception?" <- #fullException @% "valid" ]
                  @%[ "exceptionCause" <- #fullException @% "data" ]
                  @%[ "pcMemAddr" <- #newAddr ]
                  @%[ "memCap?" <- $$isCap ]
                  @%[ "memSize" <- Const ty (natToWord MemSizeSz size) ]
                  @%[ "mem?" <- $$true ]
                  @%[ "ldSigned?" <- $$sign ]
                  @%[ "ldPerms" <- #perms ]));
      instProperties := DefProperties<| hasCs1 := true |>
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
      inputXform ty pc inst cs1 cs2 scr csr :=
        ( LETC newAddr <- (cs1 @% "val") + SignExtendTruncLsb Xlen ({< funct7 inst, rdFixed inst >});
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
                                                (isNotZero
                                                   (ZeroExtendTruncLsb (Nat.log2_up ((Xlen + CapSz)/8))#newAddr))
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
      instProperties := DefProperties<| hasCs1 := true |><| hasCs2 := true |>
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
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( LETC newAddr <- (pc @% "val") + SignExtendTruncLsb Xlen (jalOffset inst);
              LETC linkAddr <- (pc @% "val") + ITE (isInstNotCompressed inst) $4 $2;
              LETC mstatusArr <- unpack (Array (S (Xlen-1)) Bool) (castBits XlenSXlenMinus1 csr);
              LETC ie <- #mstatusArr ![ 3 ];
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdTag" <- $$true ]
                      @%[ "cdCap" <- seal capAccessors (getOTypeFromIe capAccessors #ie) (pc @% "cap") ]
                      @%[ "cdVal" <- #linkAddr ]
                      @%[ "taken?" <- $$true ]
                      @%[ "pcMemAddr" <- #newAddr ]
                      @%[ "exception?" <- if compressed
                                          then $$false
                                          else isNotZero (ZeroExtendTruncLsb 2 #newAddr) ]
                      @%[ "exceptionCause" <- if compressed
                                              then $0
                                              else Const ty (natToWord Xlen InstMisaligned) ]
                      @%[ "exceptionValue" <- #newAddr ]
                      @%[ "baseException?" <- $$true ]));
          instProperties := DefProperties <| implicitIe := true |>
        |};
        {|instName := "CJALR";
          uniqId := [fieldVal opcodeField (truncMsb (7'h"67"));
                     fieldVal funct3Field (3'h"0")];
          inputXform ty pc inst cs1 cs2 scr csr :=
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
                                 else StaticIf (negb compressed) (isNotZero (ZeroExtendTruncLsb 2 #newAddr))
                                               (mkPair (Valid (Const ty (natToWord Xlen InstMisaligned))) ($$true))
                                               (mkPair Invalid ($$false)))));
              LETC mstatusArr <- unpack (Array (S (Xlen-1)) Bool) (castBits XlenSXlenMinus1 csr);
              LETC ie <- #mstatusArr ![ 3 ];
              LETC ieSentry <- isIeSentry capAccessors (cs1 @% "cap");
              LETC idSentry <- isIdSentry capAccessors (cs1 @% "cap");
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
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
          instProperties := DefProperties<| hasCs1 := true |><| implicitIe := true |>
        |}
      ]
    |}.

  Definition isJumpInsts ty (inst: Inst @# ty) :=
    redLet (@Kor _ _) (fun x => RetE (matchUniqId inst (uniqId x))) (filterInsts [jumpInsts]).


  Definition exceptionInsts: InstEntryFull BaseOutput :=
    {|xlens := [32; 64];
      extension := Base;
      instEntries := [
        {|instName := "ECall";
          uniqId := [fieldVal opcodeField (5'b"11100");
                     fieldVal (7, 25) (_ 'h"0")];
          inputXform ty pc inst cs1 cs2 scr csr :=
              ( RetE ((DefBaseOutput ty)
                        @%[ "exception?" <- $$true ]
                        @%[ "exceptionCause" <- Const ty (natToWord Xlen ECall) ]
                        @%[ "baseException?" <- $$true ]));
          instProperties := DefProperties
        |};
        {|instName := "ERet";
          uniqId := [fieldVal opcodeField (5'b"11100");
                     fieldVal rdFixedField (5'h"0");
                     fieldVal funct3Field (3'h"0");
                     fieldVal rs1FixedField (5'h"0");
                     fieldVal rs2FixedField (5'b"00010");
                     fieldVal funct7Field (7'b"0011000")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( LETE pcPerms <- getCapPerms capAccessors (pc @% "cap");
              LETC exceptionCause <- ITE (#pcPerms @% "SR")
                                       (Const ty (natToWord Xlen CapTagViolation))
                                       (Const ty (natToWord Xlen CapSysRegViolation));
              LETC newMepc <- if compressed
                              then ZeroExtendTruncLsb Xlen
                                     ({< ZeroExtendTruncMsb (Xlen - 1) (scr @% "val"), $$WO~0 >})
                              else ZeroExtendTruncLsb Xlen
                                     ({< ZeroExtendTruncMsb (Xlen - 2) (scr @% "val"), $$(2'b"00") >});
              LETE representable <- representableFn (justFullCap scr) #newMepc;
              LETC exception <- !((scr @% "tag") && !isSealed capAccessors (scr @% "cap") && #representable
                                  && (#pcPerms @% "SR"));
              RetE ((DefBaseOutput ty)
                      @%[ "taken?" <- $$true ]
                      @%[ "pcMemAddr" <- #newMepc ]
                      @%[ "pcCap" <- scr @% "cap" ]
                      @%[ "exception?" <- #exception ]
                      @%[ "exceptionCause" <- #exceptionCause ]
                      @%[ "scrException?" <- !(#pcPerms @% "SR") ]
                      @%[ "pcCapException?" <- #pcPerms @% "SR" ]));
          instProperties := DefProperties<| implicitMepcc := true |>
        |}
      ]
    |}.

  Definition isERetInst ty (inst: Inst @# ty) :=
    redLet (@Kor _ _) (fun x => RetE (matchUniqId inst (uniqId x)))
      (filter (fun x => String.eqb (instName x) "ECall") (filterInsts [exceptionInsts])).

  Definition MTCCInit : ConstT (FullCapWithTag) := STRUCT_CONST { "tag" ::= true;
                                                                  "cap" ::= MtccCap;
                                                                  "val" ::= MtccVal }.

  Definition MTDCInit : ConstT (FullCapWithTag) := STRUCT_CONST { "tag" ::= true;
                                                                  "cap" ::= MtdcCap;
                                                                  "val" ::= MtdcVal }.

  Definition scrList : list ScrReg := [
      {|scrRegInfo := Build_RegInfo ($28)%word "MTCC" (Some (SyntaxConst MTCCInit));
        legalizeScrRead := None;
        legalizeScrWrite :=
          Some (fun ty (cs1Val scrVal: Data @# ty) =>
                  ( RetE (ZeroExtendTruncLsb Xlen ({< ZeroExtendTruncMsb (Xlen - 2) cs1Val, $$(wzero 2) >}))) );
        isImplicitScr := false |};
      {|scrRegInfo := Build_RegInfo ($29)%word "MTDC" (Some (SyntaxConst MTDCInit));
        legalizeScrRead := None;
        legalizeScrWrite := None;
        isImplicitScr := false |};
      {|scrRegInfo := Build_RegInfo ($30)%word "MScratchC" None;
        legalizeScrRead := None;
        legalizeScrWrite := None;
        isImplicitScr := false |};
      {|scrRegInfo := Build_RegInfo ($31)%word "MEPCC" None;
        legalizeScrRead :=
          Some (fun ty (scrVal: Data @# ty) =>
                  ( RetE (if compressed
                          then ZeroExtendTruncLsb Xlen
                                 ({< ZeroExtendTruncMsb (Xlen - 1) scrVal, $$WO~0 >})
                          else ZeroExtendTruncLsb Xlen
                                 ({< ZeroExtendTruncMsb (Xlen - 2) scrVal, $$(2'b"00") >}))) );
        legalizeScrWrite := None;
        isImplicitScr := true |}
    ].

  Definition scrInsts: InstEntryFull BaseOutput :=
    {|xlens := [32; 64];
      extension := Base;
      instEntries :=
        map (fun '(Build_ScrReg (Build_RegInfo addr name _) readFn writeFn isImplicit) =>
               {|instName := ("CSpecialRW_" ++ name)%string;
                 uniqId := [fieldVal opcodeField (truncMsb (5'h"5b"));
                            fieldVal funct3Field (3'h"0");
                            fieldVal rs2FixedField addr;
                            fieldVal funct7Field (7'h"1")];
                 inputXform ty pc inst cs1 cs2 scr csr :=
                   ( LETE pcPerms <- getCapPerms capAccessors (pc @% "cap");
                     LETE fixScrVal : Data <- match readFn with
                                              | Some f => f ty (scr @% "val")
                                              | None => RetE (scr @% "val")
                                              end;
                     LETE fixScrTag <- 
                       match writeFn with
                       | Some _ =>
                           ( LETE representable <- representableFn (justFullCap scr) #fixScrVal;
                             RetE (scr @% "tag" && !isSealed capAccessors (scr @% "cap") && #representable) )
                       | None => RetE (scr @% "tag")
                       end;
                     LETE fixCs1Val <- match writeFn with
                                       | Some f => f ty (cs1 @% "val") (scr @% "val")
                                       | None => RetE (cs1 @% "val")
                                       end;
                     LETE fixCs1Tag <-
                       match writeFn with
                       | Some _ =>
                           ( LETE representable <- representableFn (justFullCap cs1) #fixCs1Val;
                             RetE (cs1 @% "tag" && !isSealed capAccessors (cs1 @% "cap") && #representable) )
                       | None => RetE (cs1 @% "tag")
                       end;
                     RetE ((DefBaseOutput ty)
                             @%[ "wb?" <- $$true ]
                             @%[ "cdTag" <- #fixScrTag ]
                             @%[ "cdCap" <- scr @% "cap" ]
                             @%[ "cdVal" <- #fixScrVal ]
                             @%[ "exception?" <- !(#pcPerms @% "SR") ]
                             @%[ "exceptionCause" <- Const ty (natToWord Xlen CapSysRegViolation) ]
                             @%[ "wbScr?" <- isNotZero (rs1Fixed inst)]
                             @%[ "scrTag" <- #fixCs1Tag ]
                             @%[ "scrCap" <- cs1 @% "cap" ]
                             @%[ "scrVal" <- #fixCs1Val ]
                             @%[ "scrException?" <- $$true ]));
                 instProperties :=
                   DefProperties<| hasCs1 := true |><| hasScr := true |><| implicitMepcc := isImplicit |>
               |}) scrList
    |}.

  Definition IeInvMask n ty : Array n Bool @# ty :=
    Const ty (ConstArray (fun i => match i with
                                   | Fin.FS _ (Fin.FS _ (Fin.FS _ (Fin.F1 _))) => false
                                   | _ => true
                                   end)).

  Definition MStatusInit := if IeInit then Xlen 'h"8" else wzero Xlen.

  Definition csrList : list CsrReg := [
      {| csrRegInfo := Build_RegInfo (_ 'h"300") "MStatus" (Some (SyntaxConst MStatusInit)); isImplicitCsr := true |};
      {| csrRegInfo := Build_RegInfo (_ 'h"342") "MCause" None; isImplicitCsr := false |};
      {| csrRegInfo := Build_RegInfo (_ 'h"343") "MTVal" None; isImplicitCsr := false |} ].
  
  Definition isValidCsrs ty (inst : Inst @# ty) :=
    Kor (map (fun csr => (imm inst == Const ty (regAddr (csrRegInfo csr)))%kami_expr) csrList).

  Definition csrInsts: InstEntryFull BaseOutput :=
    {|xlens := [32; 64];
      extension := Base;
      instEntries := [
        {|instName := "CSRRW";
          uniqId := [fieldVal opcodeField (5'b"11100");
                     fieldVal funct3Field (3'b"001")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( LETC ieInvMask <- castBits (Nat.mul_1_r _) (pack (IeInvMask Xlen ty));
              LETC ieNotValid <- isNotZero ((cs1 @% "val") .& #ieInvMask);
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- csr ]
                      @%[ "exception?" <- (!isValidCsrs inst ||
                                             ((imm inst == $$(implicitCsrAddr csrList)) && #ieNotValid)) ]
                      @%[ "exceptionCause" <- Const ty (natToWord Xlen InstIllegal) ]
                      @%[ "exceptionValue" <- ZeroExtendTruncLsb Xlen inst ]
                      @%[ "baseException?" <- $$true ]
                      @%[ "wbCsr?" <- $$true ]
                      @%[ "csrVal" <- cs1 @% "val" ]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCsr := true |>
        |};
        {|instName := "CSRRS";
          uniqId := [fieldVal opcodeField (5'b"11100");
                     fieldVal funct3Field (3'b"010")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( LETC ieInvMask <- castBits (Nat.mul_1_r _) (pack (IeInvMask Xlen ty));
              LETC ieNotValid <- isNotZero ((cs1 @% "val") .& #ieInvMask);
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- csr ]
                      @%[ "exception?" <- (!isValidCsrs inst ||
                                             ((imm inst == $$(implicitCsrAddr csrList)) && #ieNotValid)) ]
                      @%[ "exceptionCause" <- Const ty (natToWord Xlen InstIllegal) ]
                      @%[ "exceptionValue" <- ZeroExtendTruncLsb Xlen inst ]
                      @%[ "baseException?" <- $$true ]
                      @%[ "wbCsr?" <- isNotZero (rs1Fixed inst) ]
                      @%[ "csrVal" <- csr .| (cs1 @% "val") ]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCsr := true |>
        |};
        {|instName := "CSRRC";
          uniqId := [fieldVal opcodeField (5'b"11100");
                     fieldVal funct3Field (3'b"011")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( LETC ieInvMask <- castBits (Nat.mul_1_r _) (pack (IeInvMask Xlen ty));
              LETC ieNotValid <- isNotZero ((cs1 @% "val") .& #ieInvMask);
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- csr ]
                      @%[ "exception?" <- (!isValidCsrs inst ||
                                             ((imm inst == $$(implicitCsrAddr csrList)) && #ieNotValid)) ]
                      @%[ "exceptionCause" <- Const ty (natToWord Xlen InstIllegal) ]
                      @%[ "exceptionValue" <- ZeroExtendTruncLsb Xlen inst ]
                      @%[ "baseException?" <- $$true ]
                      @%[ "wbCsr?" <- isNotZero (rs1Fixed inst) ]
                      @%[ "csrVal" <- csr .& ~(cs1 @% "val") ]));
          instProperties := DefProperties<| hasCs1 := true |><| hasCsr := true |>
        |};
        {|instName := "CSRRWI";
          uniqId := [fieldVal opcodeField (5'b"11100");
                     fieldVal funct3Field (3'b"101")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( LETC ieInvMask <- castBits (Nat.mul_1_r _) (pack (IeInvMask (snd rs1FixedField) ty));
              LETC ieNotValid <- isNotZero (rs1Fixed inst .& #ieInvMask);
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- csr ]
                      @%[ "exception?" <- (!isValidCsrs inst ||
                                             ((imm inst == $$(implicitCsrAddr csrList)) && #ieNotValid)) ]
                      @%[ "exceptionCause" <- Const ty (natToWord Xlen InstIllegal) ]
                      @%[ "exceptionValue" <- ZeroExtendTruncLsb Xlen inst ]
                      @%[ "baseException?" <- $$true ]
                      @%[ "wbCsr?" <- $$true ]
                      @%[ "csrVal" <- ZeroExtendTruncLsb Xlen (rs1Fixed inst) ]));
          instProperties := DefProperties<| hasCsr := true |>
        |};
        {|instName := "CSRRSI";
          uniqId := [fieldVal opcodeField (5'b"11100");
                     fieldVal funct3Field (3'b"110")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( LETC ieInvMask <- castBits (Nat.mul_1_r _) (pack (IeInvMask (snd rs1FixedField) ty));
              LETC ieNotValid <- isNotZero (rs1Fixed inst .& #ieInvMask);
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- csr ]
                      @%[ "exception?" <- (!isValidCsrs inst ||
                                             ((imm inst == $$(implicitCsrAddr csrList)) && #ieNotValid)) ]
                      @%[ "exceptionCause" <- Const ty (natToWord Xlen InstIllegal) ]
                      @%[ "exceptionValue" <- ZeroExtendTruncLsb Xlen inst ]
                      @%[ "baseException?" <- $$true ]
                      @%[ "wbCsr?" <- isNotZero (rs1Fixed inst) ]
                      @%[ "csrVal" <- csr .| ZeroExtendTruncLsb Xlen (rs1Fixed inst) ]));
          instProperties := DefProperties<| hasCsr := true |>
        |};
        {|instName := "CSRRCI";
          uniqId := [fieldVal opcodeField (5'b"11100");
                     fieldVal funct3Field (3'b"111")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( LETC ieInvMask <- castBits (Nat.mul_1_r _) (pack (IeInvMask (snd rs1FixedField) ty));
              LETC ieNotValid <- isNotZero (rs1Fixed inst .& #ieInvMask);
              RetE ((DefBaseOutput ty)
                      @%[ "wb?" <- $$true ]
                      @%[ "cdVal" <- csr ]
                      @%[ "exception?" <- (!isValidCsrs inst ||
                                             ((imm inst == $$(implicitCsrAddr csrList)) && #ieNotValid)) ]
                      @%[ "exceptionCause" <- Const ty (natToWord Xlen InstIllegal) ]
                      @%[ "exceptionValue" <- ZeroExtendTruncLsb Xlen inst ]
                      @%[ "baseException?" <- $$true ]
                      @%[ "wbCsr?" <- isNotZero (rs1Fixed inst) ]
                      @%[ "csrVal" <- csr .& ~(ZeroExtendTruncLsb Xlen (rs1Fixed inst)) ]));
          instProperties := DefProperties<| hasCsr := true |>
        |}
      ]
    |}.
  
  Definition iFenceInsts: InstEntryFull BaseOutput :=
    {|xlens := [32; 64];
      extension := Base;
      instEntries := [
        {|instName := "FenceI";
          uniqId := [fieldVal opcodeField (5'b"00011");
                     fieldVal funct3Field (3'b"001")];
          inputXform ty pc inst cs1 cs2 scr csr :=
            ( RetE ((DefBaseOutput ty)
                      @%[ "fenceI?" <- $$true ] ));
          instProperties := DefProperties
        |}
      ]
    |}.

  Definition specFuncUnits : list FuncEntry := map mkFuncEntry [
      {|funcNameFull := "base";
        localFuncInputFull := BaseOutput;
        localFuncFull ty x := baseOutputXform x;
        instsFull := [aluInsts; alu64Insts; capInsts; branchInsts;
                      ldInsts; ld32Insts; ld64Insts; stInsts; st32Insts; st64Insts;
                      jumpInsts; exceptionInsts; scrInsts; csrInsts; iFenceInsts]
      |}
    ].

  Ltac simplify_field field :=
    repeat match goal with
           | |- context [field ?P] =>
               let sth := fresh "sth" in
               let Heq_sth := fresh "Heq_sth" in
               remember (field P) as sth eqn: Heq_sth; simpl in Heq_sth; rewrite Heq_sth; clear Heq_sth sth
           end.

  Ltac checkUniq :=
    cbn [specFuncUnits concat map mkFuncEntry insts instsFull localFuncInputFull fold_left localFuncInput];
    pose proof extsHasBase;
    simplify_field (@extension procParams BaseOutput);
    destruct (in_dec Extension_eq_dec Base supportedExts);
    [| unfold getBool; rewrite ?andb_false_r; simpl; auto; constructor];
    simplify_field (@xlens procParams BaseOutput);
    let H := fresh in
    destruct (xlenIs32_or_64) as [H | H]; repeat (rewrite H; simpl);
      repeat constructor; unfold In, not; intros;
      repeat match goal with
        | H: ?p \/ ?q |- _ => destruct H; try discriminate
        end; auto.

  (* Run the following only if the uniqId field or the instName field changes for any instruction.
     (Corrollary: every time a new instruction is added, it must be run)
   *)

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
