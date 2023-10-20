Require Import Kami.AllNotations ProcKami.CheriTypes.
Require Import List.

Section Alu.
  Context `{procParams: ProcParams}.

  Definition XlenPlus1Input :=
    STRUCT_TYPE {
        "arg1" :: Bit (Xlen + 1);
        "arg2" :: Bit (Xlen + 1) }.
  
  Definition XlenInput :=
    STRUCT_TYPE {
        "arg1" :: Bit Xlen;
        "arg2" :: Bit Xlen }.

  Definition RightShiftInput :=
    STRUCT_TYPE {
        "inp" :: Bit (Xlen + 1);
        "sht" :: Bit (Nat.log2_up Xlen) }.

  Definition LeftShiftInput :=
    STRUCT_TYPE {
        "inp" :: Bit Xlen;
        "sht" :: Bit (Nat.log2_up Xlen) }.

  Definition CapInput :=
    STRUCT_TYPE {
        "addr"     :: Addr;
        "offset"   :: Addr;
        "size"     :: Bit (Nat.log2_up (S ((Xlen + CapSz)/8)));
        "zeroLsb?" :: Bool }.

  Definition CapOutput :=
    STRUCT_TYPE {
        "addr"    :: Addr;
        "base"    :: Addr;
        "top"     :: Bit (Xlen + 1);
        "perms"   :: CapPerms;
        "bounds?" :: Bool }.

  (*
    Arith: "add"
    And: "and"
    Or: "and"
    Xor: "xor"
    RightShift: "rsh"
    LeftShift: "lsh"
    Branch: "add" evaluate branch condition; "cap" new jump address; use PCC cap for exception
    JAL: "add" link address (pc+4 or pc+2); "cap" new jump address; use PCC cap for new jump address and link address and for exception; use current ie for exception
    JALR: "add" link address (pc+4 or pc+2); "cap" new jump address; use PCC cap for link address and for exception; carry RS1 cap for nextPCC;
          use current ie, RS1 tag and isNotZero imm for exception
    AUIPCC: "cap" new constructed address; use PCC cap for checking bounds of new constructed address
    AUICGP: "cap" new constructed address; use CGP's cap for checking bounds new constructed address
    LUI: carry {<imm, 12'b0>}
    CLC/CLX: "cap" Mem address; use Mem cap and Mem tag for exceptions
    CSC: "cap" Mem address; carry data val; use Mem cap, Mem tag, data tag and data cap.G for exception
    CSX: "cap" Mem address; carry data val; use Mem cap, Mem tag for exception

    1 cGetAddress: carry address
    1 cGetHigh: carry cap
    1 cGetTag: carry tag
    1 cGetBase: use cap to calculate base
    1 cGetTop: use cap to calculate top
    1 cGetLen: use cap to calculate length = top - base, saturated to 2^32-1
    1 cGetPerm: use cap to calculate perms
    1 cGetType: use cap to calculate otype

    2 cIncAddr: "cap" newAddr = addr + offset; use cap to check in-bounds and non-sealedness; use tag to reset tag on not in-bounds or sealedness
    1 cSub: "cap" newAddr = addr1 - addr2
    1 cSetAddr: carry new address; use cap to check in-bounds and non-sealedness; use tag to reset tag on not in-bounds or sealedness
    1 cMove: carry tag; carry cap; carry val
    1 cSetHigh: carry newCap; carry val; clear tag
    1 cAndPerm: use cap to AND with permsMask and to check non-sealedness; use tag to reset tag on sealedness
    1 cClearTag: carry cap; carry val

    1 cRepresentableAlignmentMask: use countLeadingZeros(val), and to see if e = 23-countLeadingZeros(val) has to be incremented by 1 iff LSB e bits are non-zero
    1 cRoundRepresentableLength: use val to calculate cRepresentableALignmentMask (=m) and return (val + ~m)&m
    3 cSetBounds: "cap" to calculate addr + length;
                  use cap to check if addr + length is in bounds;
                  use cap to check for non-sealedness;
                  use length to calculate e as in cRepresentableAlignmentMask;
                  use addr, length, e to calculate B, T and exactness;
                  use cap to update it using B, T, e
                  use tag to reset tag on sealedness or not in-bounds (or non exactness)

    1 cSetEqualExact: check equality of two tags, two caps and two vals

    1 cTestSubset: use cap1 and cap2 to get perms1, perms2, base1, base2, top1 and top2. use tag1 and tag2.
                   Return 0: If tags don't match or if base2 < base1 or top2 > top1 or perms2 is not a subset of perms1
                   Return 1: otherwise

    1 cSeal: use addr2 for calculating otype and for checking bounds
             use cap1 to check if it has permit execute and if it is sealed
             use cap2 to check if addr2 is in-bounds, cap2 is not sealed, cap2 has permit seal and permitOtype i.e.
                                                                                                   (if cap1.permit_execute then addr2 \in [1,2,3,6,7] else 9 <= addr2 <= 15)
             use tag2 to check if sealer is tagged
             use tag1 to reset tag if cap2's check or tag2's check fails or if cap1 is sealed
             use cap1 to seal based on otype given by addr2

    1 cUnseal: use addr2 for calculating otype and for checking bounds
               use cap1 to get cap1.otype and check if cap1 is sealed
               use cap2 to check if addr2 is in-bounds, cap2 is not sealed, cap2 has permit unseal, if addr2 matches cap1.otype
               use tag2 to check if sealer is tagged
               use tag1 to reset tag if cap2's check of tag2's check fails or if cap1 is unsealed
               use cap1 to unseal with global set to cap1.global && cap2.global


    "cGetX", "cClearTag", "cMove", "cSetAddr": carry val; carry cap; carry tag
    "cAndPerms": carry tag; carry cap; carry address; carry permMask
    "cIncAddr": "cap" new constructed address; carry cap; carry tag
    "cSetHigh": carry address; carry cap
    "cSub": "cap" new constructed address
    "cSetBounds": carry tag; carry old address; use old cap; use length
    "cRoundRepresentableAlignmentMask": use length
    "cRoundRepresentableLength": use length
    "cSeal": use sealer tag; use sealer cap; use sealer val; use sealee tag; use sealee cap; use sealee val
    "cUnseal": use sealer tag; use sealer cap; use sealer val; use sealee tag; use sealee cap; use sealee val
    "cSetEqualExact": compare eq of two caps; two vals and two tags
    "cTestSubset": compare two cap bases; compare two cap tops; compare two cap perms
   *)

  (* TODO:
     - Cs1Cs2Rd
       + CSetEqualExact := tag, cap and val should all match. Use xor and adder?
       + CTestSubset := both tags should be the same, cap of cs2 should be a subset of cs1 in permission and bounds.
                        Perms can be sent to "and" logic; tags sent somewhere for equality; bounds checked explicitly "somehow"
     - Cs1Cs2Cd
       + CSeal := new tag is set only if (cs1 is tagged, cs1 is unsealed, cs2 is tagged, cs2 is not sealed, cs2 permit seal, cs2 in bounds,
                                          if cs1.EX then 1 <= cs2.val <= 7 else 9 <= cs2_addr <= 15), 
       + CUnseal := new tag is set only if (cs1 is tagged, cs2 bounds check, cs2 permit unseal, cs2 not sealed, cs1 sealed and cs1.otype = cs2.val), new G = cs1.G && cs12.G
     - Rs1Rd
       + CRoundRepresentableLength := Needs "e", which is effectively countLeadingZeros of length
       + CRepresentableAlignmentMask := Needs "e" 
     - Cs1ImmCd
       + CIncAddrImm := increment address, clear tag if not in bounds
       + CSetBoundsImm
     - Cs1Rs2Cd
       + CSetBounds
       + CSetBoundsExact
   *)

  Definition BaseFuncUnitsInput :=
    STRUCT_TYPE {
        "add" :: XlenPlus1Input; (* Branch: evaluate branch condition;
                                    JAL/JALR: Link address (pc+4 or pc+2);
                                    LUI: carry {<imm, 12'b0>};
                                    CSC: carry data tag and cap *)
        "and" :: XlenInput; (* CSC: Inputs data tag and data local *)
        "xor" :: XlenInput; (* Branch/AUIPCC: carry current PCC's cap for nextPCC/new constructed address;
                               AUICGP: carry CGP's ($c3's) cap for new constructed address;
                               JAL: carry current PCC's cap for nextPCC and linking;
                               JALR: carry RS1's cap for nextPCC;
                               CLC/CLX/CSC/CSX: carry Mem cap *)
        "rsh" :: RightShiftInput; (* JAL: carry current ie_status;
                                     JALR: carry RS1's tag, isNotZero imm, current ie_status;
                                     CLC/CLX/CSC/CSX: carry Mem tag *)
        "lsh" :: LeftShiftInput; (* JALR: carry current PCC's cap for linking;
                                    CSX/CSC: carry data *)
        "cap" :: CapInput }. (* Branch/JAL: New Jump address based on current PCC;
                                AUIPCC/AUICGP: New constructed address;
                                JALR: New Jump address based on RS1;
                                CLC/CLX/CSC/CSX: Mem address *)

  Definition BaseFuncExtraInfo :=
    STRUCT_TYPE {
        "notZeroImm?" :: Bool;
        "ie?"         :: Bool;
        "tag"         :: Bool }.


  Definition BaseFuncUnitsOutput :=
    STRUCT_TYPE {
        "add" :: Bit (Xlen + 1);
        "and" :: Bit Xlen;
        "xor" :: Bit Xlen;
        "rsh" :: Bit Xlen;
        "lsh" :: Bit Xlen;
        "cap" :: CapOutput }.

  Section Ty.
    Variable ty: Kind -> Type.
    Variable pc: FullCap @# ty.
    Variable inst: Inst @# ty.
    Variable rs1 rs2: FullCapWithTag @# ty.
    
    Local Open Scope kami_expr.

    Definition packBaseFuncExtraInfo (notZeroImm ie tag: Bool @# ty) : RightShiftInput @# ty :=
      STRUCT {
          "inp" ::= ZeroExtendTruncLsb (Xlen + 1) ({< pack notZeroImm, pack ie, pack tag >});
          "sht" ::= $0 }.

    Definition unpackBaseFuncExtraInfo (data: Data @# ty) := unpack BaseFuncExtraInfo (ZeroExtendTruncLsb 3 data).

    Definition packStDataTaggedLocal (stTag stLocal: Bool @# ty) : XlenInput @# ty :=
      STRUCT {
          "arg1" ::= ZeroExtendTruncLsb Xlen (pack stTag);
          "arg2" ::= ZeroExtendTruncLsb Xlen (pack stLocal) }.

    Definition unpackStDataTaggedLocal (data: Data @# ty) := unpack Bool (ZeroExtendTruncLsb 1 data).

    Definition packDataTagCap (tag: Bool @# ty) (cap: Cap @# ty) : XlenPlus1Input @# ty :=
      STRUCT { "arg1" ::= {< pack tag, pack cap >};
               "arg2" ::= $0 }.

    Definition unpackDataTagCap (data: Bit (Xlen + 1) @# ty) := unpack (Pair Bool Cap) data.
    
    Definition DefaultXlenPlus1Input: XlenPlus1Input @# ty :=
      STRUCT {
          "arg1" ::= SignExtend 1 (rs1 @% "val");
          "arg2" ::= SignExtend 1 (rs2 @% "val") }.

    Definition DefaultXlenInput: XlenInput @# ty :=
      STRUCT {
          "arg1" ::= (rs1 @% "val");
          "arg2" ::= (rs2 @% "val") }.

    Definition DefaultRightShiftInput: RightShiftInput @# ty :=
      STRUCT {
          "inp" ::= SignExtend 1 (rs1 @% "val");
          "sht" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (rs2 @% "val") }.

    Definition DefaultLeftShiftInput: LeftShiftInput @# ty :=
      STRUCT {
          "inp" ::= (rs1 @% "val");
          "sht" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (rs2 @% "val") }.

    Definition DefaultCapInput: CapInput @# ty :=
      STRUCT {
          "addr"     ::= (rs1 @% "val");
          "offset"   ::= SignExtendTruncLsb Xlen (imm inst);
          "size"     ::= $2;
          "zeroLsb?" ::= $$false}.

    Definition DefaultBaseFuncUnitsInput: BaseFuncUnitsInput @# ty :=
      STRUCT {
          "add" ::= DefaultXlenPlus1Input;
          "and" ::= DefaultXlenInput;
          "xor" ::= DefaultXlenInput;
          "rsh" ::= DefaultRightShiftInput;
          "lsh" ::= DefaultLeftShiftInput;
          "cap" ::= DefaultCapInput }.

    Inductive InstType := BranchJal | Jalr | Clx | Csx | Clc | Csc.

    Theorem InstTypeDec: forall a b: InstType, {a = b} + {a <> b}.
    Proof.
      decide equality.
    Defined.

    Definition neg ty n (a : Bit n @# ty) := ((~ a) + $1)%kami_expr.
    Definition isNotZero ty n (a : Bit n @# ty) := unpack Bool (UniBit (UOr _) a).
    Definition isZero ty n (a : Bit n @# ty) := !(isNotZero a).

    Definition mkMaybeExceptionCause (e: nat): Pair Bool Data @# ty :=
      (STRUCT {"fst" ::= $$true; "snd" ::= $e}).

    Section StaticIf.
      Variable A B: Prop.
      Variable K: Kind.
      Definition StaticIf (filt: sumbool A B) (p: Bool @# ty) (t: K @# ty) (f: K @# ty) : K @# ty :=
        if filt
        then (IF p then t else f)%kami_expr
        else f.

      Definition StaticIf2Bool (filt1: sumbool A B) (filt2: bool) (p: Bool @# ty) (t: K @# ty) (f: K @# ty)
        : K @# ty :=
        if filt2
        then StaticIf filt1 p t f
        else f.
    End StaticIf.

    Definition mkJustExceptionExpanded (instType: InstType) (tag: Bool @# ty) (addr: Addr @# ty)
      (inBounds: Bool @# ty) (perms: CapPerms @# ty) (sealed: Bool @# ty) (sentry: Bool @# ty)
      (taken: Bool @# ty) (isNotZeroImmVal: Bool @# ty) (stDataTaggedLocal: Bool @# ty) :
      Pair Bool Data @# ty :=
      StaticIf (in_dec InstTypeDec instType [Jalr; Clx; Clc; Csx; Csc]) (!tag)
        (mkMaybeExceptionCause CapTagViolation)
        (StaticIf (in_dec InstTypeDec instType [Clx; Clc; Csx; Csc]) sealed
           (mkMaybeExceptionCause CapSealViolation)
           (StaticIf (InstTypeDec instType Jalr) (sealed && (!sentry || isNotZeroImmVal))
              (mkMaybeExceptionCause CapSealViolation)
              (StaticIf (InstTypeDec instType Jalr) (!(perms@%"EX"))
                 (mkMaybeExceptionCause CapExecViolation)
                 (StaticIf (in_dec InstTypeDec instType [Clx; Clc]) (!(perms@%"LD"))
                    (mkMaybeExceptionCause CapLdViolation)
                    (StaticIf (in_dec InstTypeDec instType [Csx; Csc]) (!(perms@%"SD"))
                       (mkMaybeExceptionCause CapStViolation)
                       (StaticIf (InstTypeDec instType Csc) (!(perms@%"MC"))
                          (mkMaybeExceptionCause CapStCapViolation)
                          (StaticIf (InstTypeDec instType Csc) (!(perms@%"SL") && stDataTaggedLocal)
                             (mkMaybeExceptionCause CapStLocalViolation)
                             (StaticIf (in_dec InstTypeDec instType [BranchJal; Jalr; Clx; Csx; Clc; Csc]) (!inBounds)
                                (mkMaybeExceptionCause CapBoundsViolation)
                                (StaticIf (InstTypeDec instType Clc)
                                   (isNotZero (ZeroExtendTruncLsb (Nat.log2_up ((Xlen+CapSz)/8)) addr))
                                   (mkMaybeExceptionCause CapLdMisaligned)
                                   (StaticIf (InstTypeDec instType Csc)
                                      (isNotZero (ZeroExtendTruncLsb (Nat.log2_up ((Xlen+CapSz)/8)) addr))
                                      (mkMaybeExceptionCause CapStMisaligned)
                                      (StaticIf2Bool (in_dec InstTypeDec instType [BranchJal; Jalr]) (negb compressed)
                                         (taken && isNotZero (UniBit (TruncMsb 1 1) (ZeroExtendTruncLsb 2 addr)))
                                         (mkMaybeExceptionCause InstMisaligned)
                                         (STRUCT {"fst" ::= $$false; "snd" ::= $0})
        ))))))))))).

    Definition mkJustException (instType: InstType) (tag: Bool @# ty) (cap: Cap @# ty) (perms: CapPerms @# ty)
      (addr: Addr @# ty) (inBounds: Bool @# ty) (taken: Bool @# ty) (isNotZeroImmVal: Bool @# ty)
      (stDataTaggedLocal: Bool @# ty) : Pair Bool Data ## ty :=
      (LETC sealed <- isSealed capAccessors cap;
       LETC sentry <- isSentry capAccessors cap;
       RetE (mkJustExceptionExpanded instType tag addr inBounds perms #sealed #sentry
               taken isNotZeroImmVal stDataTaggedLocal)).

    Definition CapFuncUnit (inp: CapInput @# ty) (cap: Cap @# ty): CapOutput ## ty :=
      (LETC newAddr1 : Bit (Xlen + 1) <- ZeroExtend 1 (inp @% "addr") + ZeroExtend 1 (inp @% "offset");
       LETC newAddr : Bit (Xlen + 1) <- (IF inp @% "zeroLsb?"
                                         then castBits (Nat.add_comm 1 Xlen) ({< ZeroExtendTruncMsb Xlen #newAddr1, $$WO~0 >})
                                         else #newAddr1);
       LETC truncNewAddr: Addr <- UniBit (TruncLsb Xlen 1) #newAddr;
       LETC lastAddr : Bit (Xlen + 1) <- #newAddr + ZeroExtendTruncLsb (Xlen + 1) (inp @% "size");
       LETE capBase <- getCapBase capAccessors cap (inp @% "addr");
       LETE capTop <- getCapTop capAccessors cap (inp @% "addr");
       LETE capPerms <- getPerms capAccessors cap;
       RetE ((STRUCT {
                  "addr"    ::= #truncNewAddr;
                  "base"    ::= #capBase;
                  "top"     ::= #capTop;
                  "perms"   ::= #capPerms;
                  "bounds?" ::= ((#truncNewAddr >= #capBase) && (#lastAddr <= #capTop)) }) : CapOutput @# ty)).

    Definition BaseFuncUnits (inp: BaseFuncUnitsInput ## ty) :=
      (LETE i <- inp;
       LETE cap <- CapFuncUnit (#i @% "cap") (#i @% "xor" @% "arg1");
       RetE (STRUCT {
                 "add" ::= ((#i @% "add" @% "arg1")  + (#i @% "add" @% "arg2"));
                 "and" ::= ((#i @% "and" @% "arg1") .& (#i @% "and" @% "arg2"));
                 "xor" ::= ((#i @% "xor" @% "arg1") .^ (#i @% "xor" @% "arg2"));
                 "rsh" ::= UniBit (TruncLsb Xlen 1)
                             ((#i @% "rsh" @% "inp") >>> (#i @% "rsh" @% "sht"));
                 "lsh" ::= ((#i @% "lsh" @% "inp") << (#i @% "lsh" @% "sht"));
                 "cap" ::= #cap } : BaseFuncUnitsOutput @# ty)).
  End Ty.

  Local Open Scope kami_expr.
  Local Open Scope list_scope.

  Definition arithEntries: list (InstEntry BaseFuncUnitsInput BaseFuncUnitsOutput) := [
      {|instName     := "addi" ;
        xlens        := [32; 64];
        extensions   := [Base];
        uniqId       := [fieldVal opcodeField ('b"00100");
                         fieldVal funct3Field ('b"000")] ;
        inputXform ty pc inst rs1 rs2 ie :=
          (LETC addIn : XlenPlus1Input <-
                          STRUCT { "arg1" ::= SignExtend 1 (rs1 @% "val");
                                   "arg2" ::= SignExtendTruncLsb (Xlen + 1) (imm inst) };
           RetE ((DefaultBaseFuncUnitsInput inst rs1 rs2)@%[ "add" <- #addIn ]));
        outputXform ty (res : BaseFuncUnitsOutput @# ty) :=
          (LETC ret <- UniBit (TruncLsb Xlen 1) (res @% "add");
           RetE (mkIntReg #ret (res @% "xor") (res @% "cap" @% "addr")));
        instProperties := {| hasRs1 := true; hasRs2 := false; implicit := 0 |}
      |};
      {|instName     := "slti" ;
        xlens        := [32; 64];
        extensions   := [Base];
        uniqId       := [fieldVal opcodeField ('b"00100");
                         fieldVal funct3Field ('b"010")];
        inputXform ty pc inst rs1 rs2 ie :=
          (LETC addIn : XlenPlus1Input <-
                          STRUCT { "arg1" ::= SignExtend 1 (rs1 @% "val");
                                   "arg2" ::= neg (SignExtendTruncLsb (Xlen + 1) (imm inst)) };
           RetE ((DefaultBaseFuncUnitsInput inst rs1 rs2)@%[ "add" <- #addIn ]));
        outputXform ty (res : BaseFuncUnitsOutput @# ty) :=
          (LETC ret <- UniBit (TruncMsb Xlen 1) (res @% "add");
           RetE (mkIntReg (ZeroExtendTruncLsb Xlen #ret) (res @% "xor") (res @% "cap" @% "addr")));
        instProperties := {| hasRs1 := true; hasRs2 := false; implicit := 0 |}
      |};
      {|instName     := "sltiu" ;
        xlens        := [32; 64];
        extensions   := [Base];
        uniqId       := [fieldVal opcodeField ('b"00100");
                         fieldVal funct3Field ('b"011")];
        inputXform ty pc inst rs1 rs2 ie :=
          (LETC addIn : XlenPlus1Input <-
                          STRUCT { "arg1" ::= ZeroExtend 1 (rs1 @% "val");
                                   "arg2" ::= neg (ZeroExtendTruncLsb (Xlen + 1) (imm inst)) };
           RetE ((DefaultBaseFuncUnitsInput inst rs1 rs2)@%[ "add" <- #addIn ]));
        outputXform ty (res : BaseFuncUnitsOutput @# ty) :=
          (LETC ret <- UniBit (TruncMsb Xlen 1) (res @% "add");
           RetE (mkIntReg (ZeroExtendTruncLsb Xlen #ret) (res @% "xor") (res @% "cap" @% "addr")));
        instProperties := {| hasRs1 := true; hasRs2 := false; implicit := 0 |}
      |};
      {|instName     := "add" ;
        xlens        := [32; 64];
        extensions   := [Base];
        uniqId       := [fieldVal opcodeField ('b"01100");
                         fieldVal funct3Field ('b"000");
                         fieldVal funct7Field ('b"0000000")];
        inputXform ty pc inst rs1 rs2 ie :=
          (LETC addIn : XlenPlus1Input <-
                          STRUCT { "arg1" ::= SignExtend 1 (rs1 @% "val");
                                   "arg2" ::= SignExtend 1 (rs2 @% "val") };
           RetE ((DefaultBaseFuncUnitsInput inst rs1 rs2)@%[ "add" <- #addIn ]));
        outputXform ty (res : BaseFuncUnitsOutput @# ty) :=
          (LETC ret <- UniBit (TruncLsb Xlen 1) (res @% "add");
           RetE (mkIntReg #ret (res @% "xor") (res @% "cap" @% "addr")));
        instProperties := {| hasRs1 := true; hasRs2 := true; implicit := 0 |}
      |};
      {|instName     := "sub" ;
        xlens        := [32; 64];
        extensions   := [Base];
        uniqId       := [fieldVal opcodeField ('b"01100");
                         fieldVal funct3Field ('b"000");
                         fieldVal funct7Field ('b"0000000")];
        inputXform ty pc inst rs1 rs2 ie :=
          (LETC addIn : XlenPlus1Input <-
                          STRUCT { "arg1" ::= SignExtend 1 (rs1 @% "val");
                                   "arg2" ::= neg (SignExtend 1 (rs2 @% "val")) };
           RetE ((DefaultBaseFuncUnitsInput inst rs1 rs2)@%[ "add" <- #addIn ]));
        outputXform ty (res : BaseFuncUnitsOutput @# ty) :=
          (LETC ret <- UniBit (TruncLsb Xlen 1) (res @% "add");
           RetE (mkIntReg #ret (res @% "xor") (res @% "cap" @% "addr")));
        instProperties := {| hasRs1 := true; hasRs2 := true; implicit := 0 |}
      |};
      {|instName     := "slt" ;
        xlens        := [32; 64];
        extensions   := [Base];
        uniqId       := [fieldVal opcodeField ('b"01100");
                         fieldVal funct3Field ('b"010");
                         fieldVal funct7Field ('b"0000000")];
        inputXform ty pc inst rs1 rs2 ie :=
          (LETC addIn : XlenPlus1Input <-
                          STRUCT { "arg1" ::= SignExtend 1 (rs1 @% "val");
                                   "arg2" ::= neg (SignExtend 1 (rs2 @% "val")) };
           RetE ((DefaultBaseFuncUnitsInput inst rs1 rs2)@%[ "add" <- #addIn ]));
        outputXform ty (res : BaseFuncUnitsOutput @# ty) :=
          (LETC ret <- UniBit (TruncMsb Xlen 1) (res @% "add");
           RetE (mkIntReg (ZeroExtendTruncLsb Xlen #ret) (res @% "xor") (res @% "cap" @% "addr")));
        instProperties := {| hasRs1 := true; hasRs2 := true; implicit := 0 |}
      |};
      {|instName     := "sltu" ;
        xlens        := [32; 64];
        extensions   := [Base];
        uniqId       := [fieldVal opcodeField ('b"01100");
                         fieldVal funct3Field ('b"011");
                         fieldVal funct7Field ('b"0000000")];
        inputXform ty pc inst rs1 rs2 ie :=
          (LETC addIn : XlenPlus1Input <-
                          STRUCT { "arg1" ::= ZeroExtend 1 (rs1 @% "val");
                                   "arg2" ::= neg (ZeroExtend 1 (rs2 @% "val")) };
           RetE ((DefaultBaseFuncUnitsInput inst rs1 rs2)@%[ "add" <- #addIn ]));
        outputXform ty (res : BaseFuncUnitsOutput @# ty) :=
          (LETC ret <- UniBit (TruncMsb Xlen 1) (res @% "add");
           RetE (mkIntReg (ZeroExtendTruncLsb Xlen #ret) (res @% "xor") (res @% "cap" @% "addr")));
        instProperties := {| hasRs1 := true; hasRs2 := true; implicit := 0 |}
      |};
      {|instName     := "addiw" ;
        xlens        := [64];
        extensions   := [Base];
        uniqId       := [fieldVal opcodeField ('b"00110");
                         fieldVal funct3Field ('b"000")];
        inputXform ty pc inst rs1 rs2 ie :=
          (LETC addIn : XlenPlus1Input <-
                          STRUCT { "arg1" ::= ZeroExtend 1 (rs1 @% "val");
                                   "arg2" ::= ZeroExtendTruncLsb (Xlen + 1) (imm inst) };
           RetE ((DefaultBaseFuncUnitsInput inst rs1 rs2)@%[ "add" <- #addIn ]));
        outputXform ty (res : BaseFuncUnitsOutput @# ty) :=
          (LETC ret <- ZeroExtendTruncLsb 32 (res @% "add");
           RetE (mkIntReg (ZeroExtendTruncLsb Xlen #ret) (res @% "xor") (res @% "cap" @% "addr")));
        instProperties := {| hasRs1 := true; hasRs2 := false; implicit := 0 |}
      |};
      {|instName     := "addw" ;
        xlens        := [64];
        extensions   := [Base];
        uniqId       := [fieldVal opcodeField ('b"01110");
                         fieldVal funct3Field ('b"000"); 
                         fieldVal funct7Field ('b"0000000")];
        inputXform ty pc inst rs1 rs2 ie :=
          (LETC addIn : XlenPlus1Input <-
                          STRUCT { "arg1" ::= ZeroExtend 1 (rs1 @% "val");
                                   "arg2" ::= ZeroExtend 1 (rs2 @% "val") };
           RetE ((DefaultBaseFuncUnitsInput inst rs1 rs2)@%[ "add" <- #addIn ]));
        outputXform ty (res : BaseFuncUnitsOutput @# ty) :=
          (LETC ret <- ZeroExtendTruncLsb 32 (res @% "add");
           RetE (mkIntReg (ZeroExtendTruncLsb Xlen #ret) (res @% "xor") (res @% "cap" @% "addr")));
        instProperties := {| hasRs1 := true; hasRs2 := true; implicit := 0 |}
      |};
      {|instName     := "subw" ;
        xlens        := [64];
        extensions   := [Base];
        uniqId       := [fieldVal opcodeField ('b"01110");
                         fieldVal funct3Field ('b"000");
                         fieldVal funct7Field ('b"0100000")];
        inputXform ty pc inst rs1 rs2 ie :=
          (LETC addIn : XlenPlus1Input <-
                          STRUCT { "arg1" ::= ZeroExtend 1 (rs1 @% "val");
                                   "arg2" ::= neg (ZeroExtend 1 (rs2 @% "val")) };
           RetE ((DefaultBaseFuncUnitsInput inst rs1 rs2)@%[ "add" <- #addIn ]));
        outputXform ty (res : BaseFuncUnitsOutput @# ty) :=
          (LETC ret <- ZeroExtendTruncLsb 32 (res @% "add");
           RetE (mkIntReg (ZeroExtendTruncLsb Xlen #ret) (res @% "xor") (res @% "cap" @% "addr")));
        instProperties := {| hasRs1 := true; hasRs2 := true; implicit := 0 |}
      |}].

  Definition logicalEntries: list (InstEntry BaseFuncUnitsInput BaseFuncUnitsOutput) := [
      {|instName     := "xori";
        xlens        := [32; 64];
        extensions   := [Base];
        uniqId       := [fieldVal opcodeField ('b"00100");
                         fieldVal funct3Field ('b"100")];
        inputXform ty pc inst rs1 rs2 ie :=
          (LETC xorIn : XlenInput <-
                          STRUCT { "arg1" ::= rs1 @% "val";
                                   "arg2" ::= SignExtendTruncLsb Xlen (imm inst) };
           RetE ((DefaultBaseFuncUnitsInput inst rs1 rs2)@%[ "xor" <- #xorIn ]));
        outputXform ty (res : BaseFuncUnitsOutput @# ty) :=
          (RetE (mkIntReg (res @% "xor") (res @% "xor") (res @% "cap" @% "addr")));
        instProperties := {| hasRs1 := true; hasRs2 := false; implicit := 0 |}
      |};
      {|instName     := "ori";
        xlens        := [32; 64];
        extensions   := [Base];
        uniqId       := [fieldVal opcodeField ('b"00100");
                         fieldVal funct3Field ('b"110")];
        inputXform ty pc inst rs1 rs2 ie :=
          (LETC andIn : XlenInput <-
                          STRUCT { "arg1" ::= ~ (rs1 @% "val");
                                   "arg2" ::= ~ (SignExtendTruncLsb Xlen (imm inst)) };
           RetE ((DefaultBaseFuncUnitsInput inst rs1 rs2)@%[ "and" <- #andIn ]));
        outputXform ty (res : BaseFuncUnitsOutput @# ty) :=
          (RetE (mkIntReg (~ (res @% "and")) (res @% "xor") (res @% "cap" @% "addr")));
        instProperties := {| hasRs1 := true; hasRs2 := false; implicit := 0 |}
      |};
      {|instName     := "andi";
        xlens        := [32; 64];
        extensions   := [Base];
        uniqId       := [fieldVal opcodeField ('b"00100");
                         fieldVal funct3Field ('b"111")];
        inputXform ty pc inst rs1 rs2 ie :=
          (LETC andIn : XlenInput <-
                          STRUCT { "arg1" ::= rs1 @% "val";
                                   "arg2" ::= SignExtendTruncLsb Xlen (imm inst) };
           RetE ((DefaultBaseFuncUnitsInput inst rs1 rs2)@%[ "and" <- #andIn ]));
        outputXform ty (res : BaseFuncUnitsOutput @# ty) :=
          (RetE (mkIntReg (res @% "and") (res @% "xor") (res @% "cap" @% "addr")));
        instProperties := {| hasRs1 := true; hasRs2 := false; implicit := 0 |}
      |};
      {|instName     := "xor";
        xlens        := [32; 64];
        extensions   := [Base];
        uniqId       := [fieldVal opcodeField ('b"01100");
                         fieldVal funct3Field ('b"100");
                         fieldVal funct7Field ('b"0000000")];
        inputXform ty pc inst rs1 rs2 ie :=
          (LETC xorIn : XlenInput <-
                          STRUCT { "arg1" ::= rs1 @% "val";
                                   "arg2" ::= rs2 @% "val" };
           RetE ((DefaultBaseFuncUnitsInput inst rs1 rs2)@%[ "xor" <- #xorIn ]));
        outputXform ty (res : BaseFuncUnitsOutput @# ty) :=
          (RetE (mkIntReg (res @% "xor") (res @% "xor") (res @% "cap" @% "addr")));
        instProperties := {| hasRs1 := true; hasRs2 := true; implicit := 0 |}
      |};
      {|instName     := "or";
        xlens        := [32; 64];
        extensions   := [Base];
        uniqId       := [fieldVal opcodeField ('b"01100");
                         fieldVal funct3Field ('b"110");
                         fieldVal funct7Field ('b"0000000")];
        inputXform ty pc inst rs1 rs2 ie :=
          (LETC andIn : XlenInput <-
                          STRUCT { "arg1" ::= ~ (rs1 @% "val");
                                   "arg2" ::= ~ (rs2 @% "val") };
           RetE ((DefaultBaseFuncUnitsInput inst rs1 rs2)@%[ "and" <- #andIn ]));
        outputXform ty (res : BaseFuncUnitsOutput @# ty) :=
          (RetE (mkIntReg (~ (res @% "and")) (res @% "xor") (res @% "cap" @% "addr")));
        instProperties := {| hasRs1 := true; hasRs2 := true; implicit := 0 |}
      |};
      {|instName     := "and";
        xlens        := [32; 64];
        extensions   := [Base];
        uniqId       := [fieldVal opcodeField ('b"01100");
                         fieldVal funct3Field ('b"111");
                         fieldVal funct7Field ('b"0000000")];
        inputXform ty pc inst rs1 rs2 ie :=
          (LETC andIn : XlenInput <-
                          STRUCT { "arg1" ::= rs1 @% "val";
                                   "arg2" ::= rs2 @% "val" };
           RetE ((DefaultBaseFuncUnitsInput inst rs1 rs2)@%[ "and" <- #andIn ]));
        outputXform ty (res : BaseFuncUnitsOutput @# ty) :=
          (RetE (mkIntReg (res @% "and") (res @% "xor") (res @% "cap" @% "addr")));
        instProperties := {| hasRs1 := true; hasRs2 := true; implicit := 0 |}
      |}].

  Definition shiftEntries: list (InstEntry BaseFuncUnitsInput BaseFuncUnitsOutput) := [
      {|instName     := "slli32";
        xlens        := [32];
        extensions   := [Base];
        uniqId       := [fieldVal opcodeField ('b"00100");
                         fieldVal funct3Field ('b"001");
                         fieldVal funct7Field ('b"0000000")];
        inputXform ty pc inst rs1 rs2 ie :=
          (LETC lshIn : LeftShiftInput <-
                          STRUCT { "inp" ::= rs1 @% "val";
                                   "sht" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm inst) };
           RetE ((DefaultBaseFuncUnitsInput inst rs1 rs2)@%[ "lsh" <- #lshIn ]));
        outputXform ty (res : BaseFuncUnitsOutput @# ty) :=
          (RetE (mkIntReg (res @% "lsh") (res @% "xor") (res @% "cap" @% "addr")));
        instProperties := {| hasRs1 := true; hasRs2 := false; implicit := 0 |}
      |};
      {|instName     := "slli64";
        xlens        := [64];
        extensions   := [Base];
        uniqId       := [fieldVal opcodeField ('b"00100");
                         fieldVal funct3Field ('b"001");
                         fieldVal funct6Field ('b"000000")];
        inputXform ty pc inst rs1 rs2 ie :=
          (LETC lshIn : LeftShiftInput <-
                          STRUCT { "inp" ::= rs1 @% "val";
                                   "sht" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm inst) };
           RetE ((DefaultBaseFuncUnitsInput inst rs1 rs2)@%[ "lsh" <- #lshIn ]));
        outputXform ty (res : BaseFuncUnitsOutput @# ty) :=
          (RetE (mkIntReg (res @% "lsh") (res @% "xor") (res @% "cap" @% "addr")));
        instProperties := {| hasRs1 := true; hasRs2 := false; implicit := 0 |}
      |};
      {|instName     := "srli";
        xlens        := [32; 64];
        extensions   := [Base];
        uniqId       := [fieldVal opcodeField ('b"00100");
                         fieldVal funct3Field ('b"101");
                         fieldVal funct6Field ('b"000000")];
        inputXform ty pc inst rs1 rs2 ie :=
          (LETC rshIn : RightShiftInput <-
                          STRUCT { "inp" ::= ZeroExtend 1 (rs1 @% "val");
                                   "sht" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm inst) };
           RetE ((DefaultBaseFuncUnitsInput inst rs1 rs2)@%[ "rsh" <- #rshIn ]));
        outputXform ty (res : BaseFuncUnitsOutput @# ty) :=
          (RetE (mkIntReg (res @% "rsh") (res @% "xor") (res @% "cap" @% "addr")));
        instProperties := {| hasRs1 := true; hasRs2 := false; implicit := 0 |}
      |};
      {|instName     := "srai";
        xlens        := [32; 64];
        extensions   := [Base];
        uniqId       := [fieldVal opcodeField ('b"00100");
                         fieldVal funct3Field ('b"101");
                         fieldVal funct6Field ('b"010000")];
        inputXform ty pc inst rs1 rs2 ie :=
          (LETC rshIn : RightShiftInput <-
                          STRUCT { "inp" ::= SignExtend 1 (rs1 @% "val");
                                   "sht" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm inst) };
           RetE ((DefaultBaseFuncUnitsInput inst rs1 rs2)@%[ "rsh" <- #rshIn ]));
        outputXform ty (res : BaseFuncUnitsOutput @# ty) :=
          (RetE (mkIntReg (res @% "rsh") (res @% "xor") (res @% "cap" @% "addr")));
        instProperties := {| hasRs1 := true; hasRs2 := false; implicit := 0 |}
      |};
      {|instName     := "sll";
        xlens        := [32; 64];
        extensions   := [Base];
        uniqId       := [fieldVal opcodeField ('b"01100");
                         fieldVal funct3Field ('b"001");
                         fieldVal funct6Field ('b"000000")];
        inputXform ty pc inst rs1 rs2 ie :=
          (LETC lshIn : LeftShiftInput <-
                          STRUCT { "inp" ::= rs1 @% "val";
                                   "sht" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (rs2 @% "val") };
           RetE ((DefaultBaseFuncUnitsInput inst rs1 rs2)@%[ "lsh" <- #lshIn ]));
        outputXform ty (res : BaseFuncUnitsOutput @# ty) :=
          (RetE (mkIntReg (res @% "lsh") (res @% "xor") (res @% "cap" @% "addr")));
        instProperties := {| hasRs1 := true; hasRs2 := true; implicit := 0 |}
      |};
      {|instName     := "srl";
        xlens        := [32; 64];
        extensions   := [Base];
        uniqId       := [fieldVal opcodeField ('b"01100");
                         fieldVal funct3Field ('b"101");
                         fieldVal funct6Field ('b"000000")];
        inputXform ty pc inst rs1 rs2 ie :=
          (LETC rshIn : RightShiftInput <-
                          STRUCT { "inp" ::= ZeroExtend 1 (rs1 @% "val");
                                   "sht" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (rs2 @% "val") };
           RetE ((DefaultBaseFuncUnitsInput inst rs1 rs2)@%[ "rsh" <- #rshIn ]));
        outputXform ty (res : BaseFuncUnitsOutput @# ty) :=
          (RetE (mkIntReg (res @% "rsh") (res @% "xor") (res @% "cap" @% "addr")));
        instProperties := {| hasRs1 := true; hasRs2 := true; implicit := 0 |}
      |};
      {|instName     := "sra";
        xlens        := [32; 64];
        extensions   := [Base];
        uniqId       := [fieldVal opcodeField ('b"01100");
                         fieldVal funct3Field ('b"101");
                         fieldVal funct6Field ('b"010000")];
        inputXform ty pc inst rs1 rs2 ie :=
          (LETC rshIn : RightShiftInput <-
                          STRUCT { "inp" ::= SignExtend 1 (rs1 @% "val");
                                   "sht" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (rs2 @% "val") };
           RetE ((DefaultBaseFuncUnitsInput inst rs1 rs2)@%[ "rsh" <- #rshIn ]));
        outputXform ty (res : BaseFuncUnitsOutput @# ty) :=
          (RetE (mkIntReg (res @% "rsh") (res @% "xor") (res @% "cap" @% "addr")));
        instProperties := {| hasRs1 := true; hasRs2 := true; implicit := 0 |}
      |};
      {|instName     := "slliw";
        xlens        := [64];
        extensions   := [Base];
        uniqId       := [fieldVal opcodeField ('b"00110");
                         fieldVal funct3Field ('b"001");
                         fieldVal funct7Field ('b"0000000")];
        inputXform ty pc inst rs1 rs2 ie :=
          (LETC lshIn : LeftShiftInput <-
                          STRUCT { "inp" ::= rs1 @% "val";
                                   "sht" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm inst) };
           RetE ((DefaultBaseFuncUnitsInput inst rs1 rs2)@%[ "lsh" <- #lshIn ]));
        outputXform ty (res : BaseFuncUnitsOutput @# ty) :=
          (LETC ret <- SignExtendTruncLsb Xlen (ZeroExtendTruncLsb 32 (res @% "lsh"));
           RetE (mkIntReg #ret (res @% "xor") (res @% "cap" @% "addr")));
        instProperties := {| hasRs1 := true; hasRs2 := false; implicit := 0 |}
      |};
      {|instName     := "srliw";
        xlens        := [64];
        extensions   := [Base];
        uniqId       := [fieldVal opcodeField ('b"00110");
                         fieldVal funct3Field ('b"101");
                         fieldVal funct7Field ('b"0000000")];
        inputXform ty pc inst rs1 rs2 ie :=
          (LETC rshIn : RightShiftInput <-
                          STRUCT { "inp" ::= ZeroExtendTruncLsb (Xlen + 1)
                                               (ZeroExtendTruncLsb 32 (rs1 @% "val"));
                                   "sht" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm inst) };
           RetE ((DefaultBaseFuncUnitsInput inst rs1 rs2)@%[ "rsh" <- #rshIn ]));
        outputXform ty (res : BaseFuncUnitsOutput @# ty) :=
          (LETC ret <- SignExtendTruncLsb Xlen (ZeroExtendTruncLsb 32 (res @% "rsh"));
           RetE (mkIntReg #ret (res @% "xor") (res @% "cap" @% "addr")));
        instProperties := {| hasRs1 := true; hasRs2 := false; implicit := 0 |}
      |};
      {|instName     := "sraiw";
        xlens        := [64];
        extensions   := [Base];
        uniqId       := [fieldVal opcodeField ('b"00110");
                         fieldVal funct3Field ('b"101");
                         fieldVal funct7Field ('b"0100000")];
        inputXform ty pc inst rs1 rs2 ie :=
          (LETC rshIn : RightShiftInput <-
                          STRUCT { "inp" ::= SignExtendTruncLsb (Xlen + 1)
                                               (ZeroExtendTruncLsb 32 (rs1 @% "val"));
                                   "sht" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (imm inst) };
           RetE ((DefaultBaseFuncUnitsInput inst rs1 rs2)@%[ "rsh" <- #rshIn ]));
        outputXform ty (res : BaseFuncUnitsOutput @# ty) :=
          (LETC ret <- SignExtendTruncLsb Xlen (ZeroExtendTruncLsb 32 (res @% "rsh"));
           RetE (mkIntReg #ret (res @% "xor") (res @% "cap" @% "addr")));
        instProperties := {| hasRs1 := true; hasRs2 := false; implicit := 0 |}
      |};
      {|instName     := "sllw";
        xlens        := [64];
        extensions   := [Base];
        uniqId       := [fieldVal opcodeField ('b"01110");
                         fieldVal funct3Field ('b"001");
                         fieldVal funct7Field ('b"0000000")];
        inputXform ty pc inst rs1 rs2 ie :=
          (LETC lshIn : LeftShiftInput <-
                          STRUCT { "inp" ::= rs1 @% "val";
                                   "sht" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (rs2 @% "val") };
           RetE ((DefaultBaseFuncUnitsInput inst rs1 rs2)@%[ "lsh" <- #lshIn ]));
        outputXform ty (res : BaseFuncUnitsOutput @# ty) :=
          (LETC ret <- SignExtendTruncLsb Xlen (ZeroExtendTruncLsb 32 (res @% "lsh"));
           RetE (mkIntReg #ret (res @% "xor") (res @% "cap" @% "addr")));
        instProperties := {| hasRs1 := true; hasRs2 := true; implicit := 0 |}
      |};
      {|instName     := "srlw";
        xlens        := [64];
        extensions   := [Base];
        uniqId       := [fieldVal opcodeField ('b"01110");
                         fieldVal funct3Field ('b"101");
                         fieldVal funct7Field ('b"0000000")];
        inputXform ty pc inst rs1 rs2 ie :=
          (LETC rshIn : RightShiftInput <-
                          STRUCT { "inp" ::= ZeroExtendTruncLsb (Xlen + 1)
                                               (ZeroExtendTruncLsb 32 (rs1 @% "val"));
                                   "sht" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (rs2 @% "val") };
           RetE ((DefaultBaseFuncUnitsInput inst rs1 rs2)@%[ "rsh" <- #rshIn ]));
        outputXform ty (res : BaseFuncUnitsOutput @# ty) :=
          (LETC ret <- SignExtendTruncLsb Xlen (ZeroExtendTruncLsb 32 (res @% "rsh"));
           RetE (mkIntReg #ret (res @% "xor") (res @% "cap" @% "addr")));
        instProperties := {| hasRs1 := true; hasRs2 := true; implicit := 0 |}
      |};
      {|instName     := "sraw";
        xlens        := [64];
        extensions   := [Base];
        uniqId       := [fieldVal opcodeField ('b"01110");
                         fieldVal funct3Field ('b"101");
                         fieldVal funct7Field ('b"0100000")];
        inputXform ty pc inst rs1 rs2 ie :=
          (LETC rshIn : RightShiftInput <-
                          STRUCT { "inp" ::= SignExtendTruncLsb (Xlen + 1)
                                               (ZeroExtendTruncLsb 32 (rs1 @% "val"));
                                   "sht" ::= ZeroExtendTruncLsb (Nat.log2_up Xlen) (rs2 @% "val") };
           RetE ((DefaultBaseFuncUnitsInput inst rs1 rs2)@%[ "rsh" <- #rshIn ]));
        outputXform ty (res : BaseFuncUnitsOutput @# ty) :=
          (LETC ret <- SignExtendTruncLsb Xlen (ZeroExtendTruncLsb 32 (res @% "rsh"));
           RetE (mkIntReg #ret (res @% "xor") (res @% "cap" @% "addr")));
        instProperties := {| hasRs1 := true; hasRs2 := true; implicit := 0 |}
      |}].

  Definition addressEntries: list (InstEntry BaseFuncUnitsInput BaseFuncUnitsOutput) := [
      {|instName     := "lui" ;
        xlens        := [32; 64];
        extensions   := [Base];
        uniqId       := [fieldVal opcodeField ('b"01101")];
        inputXform ty pc inst rs1 rs2 ie :=
          (LETC immVal <- {< auiLuiOffset inst, $$(natToWord 12 0) >};
           LETE addIn : XlenPlus1Input <-
                          RetE (STRUCT { "arg1" ::= SignExtendTruncLsb (Xlen + 1) #immVal;
                                         "arg2" ::= $0 });
           RetE ((DefaultBaseFuncUnitsInput inst rs1 rs2)@%[ "add" <- #addIn ]));
        outputXform ty (res : BaseFuncUnitsOutput @# ty) :=
          (LETC ret <- UniBit (TruncLsb Xlen 1) (res @% "add");
           RetE (mkIntReg #ret (res @% "xor") (res @% "cap" @% "addr")));
        instProperties := {| hasRs1 := false; hasRs2 := false; implicit := 0 |}
      |};
      {|instName     := "auicgp" ;
        xlens        := [32; 64];
        extensions   := [Base];
        uniqId       := [fieldVal opcodeField ('b"11110")];
        inputXform ty pc inst rs1 rs2 ie :=
          (LETC immVal: Bit 31 <- {< auiLuiOffset inst, $$(natToWord 11 0) >};
           LETC capIn : CapInput <-
                          STRUCT { "addr"     ::= (rs1 @% "val");
                                   "offset"   ::= SignExtendTruncLsb Xlen #immVal;
                                   "size"     ::= $0;
                                   "zeroLsb?" ::= $$false };
           LETC xorIn : XlenInput <- (STRUCT { "arg1" ::= (rs1 @% "cap");
                                               "arg2" ::= $0 });
           RetE ((DefaultBaseFuncUnitsInput inst rs1 rs2)
                   @%[ "cap" <- #capIn]
                   @%[ "xor" <- #xorIn ]));
        outputXform ty (res : BaseFuncUnitsOutput @# ty) :=
          (LETC cap <- res @% "xor";
           LETC newAddr <- res @% "cap" @% "addr"   ;
           LETC tag <- (!isSealed capAccessors #cap) && (res @% "cap" @% "bounds?");
           RetE (mkCapResult #newAddr #cap #newAddr #tag));
        instProperties := {| hasRs1 := false; hasRs2 := false; implicit := 3 |}
      |};
      {|instName     := "auipcc" ;
        xlens        := [32; 64];
        extensions   := [Base];
        uniqId       := [fieldVal opcodeField ('b"00101")];
        inputXform ty pc inst rs1 rs2 ie :=
          (LETC immVal <- {< auiLuiOffset inst, $$(natToWord 11 0) >};
           LETC capIn : CapInput <-
                          STRUCT { "addr"     ::= (pc @% "val");
                                   "offset"   ::= SignExtendTruncLsb Xlen #immVal;
                                   "size"     ::= $0;
                                   "zeroLsb?" ::= $$false };
           LETC xorIn : XlenInput <- (STRUCT { "arg1" ::= (pc @% "cap");
                                               "arg2" ::= $0 });
           RetE ((DefaultBaseFuncUnitsInput inst rs1 rs2)
                   @%[ "cap" <- #capIn]
                   @%[ "xor" <- #xorIn ]));
        outputXform ty (res : BaseFuncUnitsOutput @# ty) :=
          (LETC cap <- res @% "xor";
           LETC newAddr <- res @% "cap" @% "addr"   ;
           LETC tag <- (res @% "cap" @% "bounds?");
           RetE (mkCapResult #newAddr #cap #newAddr #tag));
        instProperties := {| hasRs1 := false; hasRs2 := false; implicit := 0 |}
      |}].

  Definition mkBranchEntry (name: string) (funct3: word 3) (signExt: bool) (takenFn: forall ty, Bit (Xlen + 1) @# ty -> Bool @# ty) :=
      {|instName     := name;
        xlens        := [32; 64];
        extensions   := [Base];
        uniqId       := [fieldVal opcodeField ('b"11000");
                         fieldVal funct3Field funct3];
        inputXform ty pc inst rs1 rs2 ie :=
          (LETC addIn : XlenPlus1Input <-
                          STRUCT { "arg1" ::= (if signExt then @SignExtend ty 1 Xlen else @ZeroExtend ty 1 Xlen) (rs1 @% "val");
                                   "arg2" ::= neg ((if signExt then @SignExtend ty 1 Xlen else @ZeroExtend ty 1 Xlen) (rs2 @% "val")) };
           LETC capIn : CapInput <-
                          STRUCT { "addr"     ::= pc @% "val";
                                   "offset"   ::= SignExtendTruncLsb Xlen (branchOffset inst);
                                   "size"     ::= $2;
                                   "zeroLsb?" ::= $$false };
           LETC xorIn : XlenInput <-
                          STRUCT { "arg1" ::= (pc @% "cap");
                                   "arg2" ::= $0 };
           RetE ((DefaultBaseFuncUnitsInput inst rs1 rs2)
                   @%[ "add" <- #addIn ]
                   @%[ "cap" <- #capIn ]
                   @%[ "xor" <- #xorIn ]));
        outputXform ty (res : BaseFuncUnitsOutput @# ty) :=
          (LETC cap <- res @% "xor";
           LETC taken <- @takenFn ty (res @% "add");
           LETC newAddr <- res @% "cap" @% "addr"   ;
           LETC capPerms <- res @% "cap" @% "perms";
           LETE exception <- mkJustException BranchJal $$true #cap #capPerms
                               #newAddr (res @% "cap" @% "bounds?") #taken $$false $$false;
           RetE (mkPc #cap #newAddr #taken #exception));
        instProperties := {| hasRs1 := true; hasRs2 := true; implicit := 0 |}
      |}.

  Definition branchEntries: list (InstEntry BaseFuncUnitsInput BaseFuncUnitsOutput) := [
      mkBranchEntry "beq" ('b"000") false (fun ty ret => isZero ret);
      mkBranchEntry "bne" ('b"001") false (fun ty ret => isNotZero ret);
      mkBranchEntry "blt" ('b"100") true  (fun ty ret => unpack Bool (UniBit (TruncMsb Xlen 1) ret));
      mkBranchEntry "bge" ('b"101") true  (fun ty ret => !(unpack Bool (UniBit (TruncMsb Xlen 1) ret)));
      mkBranchEntry "blt" ('b"110") false (fun ty ret => unpack Bool (UniBit (TruncMsb Xlen 1) ret));
      mkBranchEntry "bge" ('b"111") false (fun ty ret => !(unpack Bool (UniBit (TruncMsb Xlen 1) ret)))
    ].

  Definition jalEntries: list (InstEntry BaseFuncUnitsInput BaseFuncUnitsOutput) := [
      {|instName     := "jal";
        xlens        := [32; 64];
        extensions   := [Base];
        uniqId       := [fieldVal opcodeField ('b"11011")];
        inputXform ty pc inst rs1 rs2 ie :=
          (LETC addIn : XlenPlus1Input <-
                          STRUCT { "arg1" ::= ZeroExtend 1 (pc @% "val");
                                   "arg2" ::= IF isInstCompressed inst then $2 else $4 };
           LETC capIn : CapInput <-
                          STRUCT { "addr"     ::= pc @% "val";
                                   "offset"   ::= SignExtendTruncLsb Xlen (jalOffset inst);
                                   "size"     ::= $2;
                                   "zeroLsb?" ::= $$false };
           LETC xorIn : XlenInput <-
                          STRUCT { "arg1" ::= (pc @% "cap");
                                   "arg2" ::= $0 };
           LETC rshIn : RightShiftInput <- packBaseFuncExtraInfo (isNotZero (imm inst)) ie (rs1 @% "tag");
           RetE ((DefaultBaseFuncUnitsInput inst rs1 rs2)
                   @%[ "add" <- #addIn ]
                   @%[ "cap" <- #capIn ]
                   @%[ "xor" <- #xorIn ]
                   @%[ "rsh" <- #rshIn ]));
        outputXform ty (res : BaseFuncUnitsOutput @# ty) :=
          (LETC linkAddr <- UniBit (TruncLsb Xlen 1) (res @% "add");
           LETC nextPcLinkCap <- res @% "xor";
           LETC taken <- $$true;
           LETC nextPcAddr <- res @% "cap" @% "addr"   ;
           LETC nextPcLinkCapPerms <- res @% "cap" @% "perms";
           LETC currIe <- (unpackBaseFuncExtraInfo (res @% "rsh")) @% "ie?";
           LETE exception <- mkJustException BranchJal $$true #nextPcLinkCap #nextPcLinkCapPerms
                               #nextPcAddr (res @% "cap" @% "bounds?") #taken $$false
                               (unpack Bool (ZeroExtendTruncLsb 1 (res @% "and")));
           LETC sealedLinkCap <- seal capAccessors #nextPcLinkCap #currIe;
           RetE (mkIntRegAndPc #linkAddr #nextPcLinkCap #nextPcAddr ($$true) #sealedLinkCap #exception true $$false $$false));
        instProperties := {| hasRs1 := false; hasRs2 := false; implicit := 0 |}
      |};
      {|instName     := "jalr";
        xlens        := [32; 64];
        extensions   := [Base];
        uniqId       := [fieldVal opcodeField ('b"11001");
                         fieldVal funct3Field ('b"000")];
        inputXform ty pc inst rs1 rs2 ie :=
          (LETC addIn : XlenPlus1Input <-
                          STRUCT { "arg1" ::= ZeroExtend 1 (pc @% "val");
                                   "arg2" ::= IF isInstCompressed inst then $2 else $4 };
           LETC capIn : CapInput <-
                          STRUCT { "addr"     ::= (rs1 @% "val");
                                   "offset"   ::= SignExtendTruncLsb Xlen (imm inst);
                                   "size"     ::= $2;
                                   "zeroLsb?" ::= $$true };
           LETC xorIn : XlenInput <-
                          STRUCT { "arg1" ::= rs1 @% "cap";
                                   "arg2" ::= $0 };
           LETC lshIn : LeftShiftInput <-
                          STRUCT { "inp" ::= (pc @% "cap");
                                   "sht" ::= $0 };
           LETC rshIn : RightShiftInput <- packBaseFuncExtraInfo (isNotZero (imm inst)) ie (rs1 @% "tag");
           RetE ((DefaultBaseFuncUnitsInput inst rs1 rs2)
                   @%[ "add" <- #addIn ]
                   @%[ "cap" <- #capIn ]
                   @%[ "xor" <- #xorIn ]
                   @%[ "lsh" <- #lshIn ]
                   @%[ "rsh" <- #rshIn ]));
        outputXform ty (res : BaseFuncUnitsOutput @# ty) :=
          (LETC linkAddr <- UniBit (TruncLsb Xlen 1) (res @% "add");
           LETC nextPcCap <- res @% "xor";
           LETC linkCap <- res @% "lsh";
           LETC taken <- $$true;
           LETC nextPcAddr <- res @% "cap" @% "addr"   ;
           LETC nextPcCapPerms <- res @% "cap" @% "perms";
           LETC notZeroImmIeTag <- unpackBaseFuncExtraInfo (res @% "rsh");
           LETC nextPcTag <- #notZeroImmIeTag @% "tag";
           LETC notZeroImm <- #notZeroImmIeTag @% "notZeroImm?";
           LETC currIe <- #notZeroImmIeTag @% "ie?";
           LETE exception <- mkJustException Jalr #nextPcTag #nextPcCap #nextPcCapPerms
                               #nextPcAddr (res @% "cap" @% "bounds?") #taken #notZeroImm
                               (unpack Bool (ZeroExtendTruncLsb 1 (res @% "and")));
           LETC sealedLinkCap <- seal capAccessors #linkCap #currIe;
           LETC changeIe <- isIeSentry capAccessors #nextPcCap || isIdSentry capAccessors #nextPcCap;
           LETC nextPcIe <- isIeSentry capAccessors #nextPcCap;
           RetE (mkIntRegAndPc #linkAddr #nextPcCap #nextPcAddr ($$true) #sealedLinkCap #exception false #changeIe #nextPcIe));
        instProperties := {| hasRs1 := true; hasRs2 := false; implicit := 0 |}
      |}].

  Definition mkLdEntry (name: string) (funct3Val: word 3) (size: nat) (signExt: bool) (accessTag: bool) :=
    {|instName     := name;
      xlens        := if (orb ((size * 8) <? 32) (andb signExt (size * 8 =? 32))) then [32; 64] else [64];
      extensions   := [Base];
      uniqId       := [fieldVal opcodeField ('b"00000");
                       fieldVal funct3Field funct3Val];
      inputXform ty pc inst rs1 rs2 ie :=
        (LETC capIn : CapInput <-
                        STRUCT { "addr"     ::= rs1 @% "val";
                                 "offset"   ::= SignExtendTruncLsb Xlen (imm inst);
                                 "size"     ::= $size;
                                 "zeroLsb?" ::= $$false };
         LETC xorIn : XlenInput <-
                        STRUCT { "arg1" ::= (rs1 @% "cap");
                                 "arg2" ::= $0 };
         LETC rshIn : RightShiftInput <- packBaseFuncExtraInfo (isNotZero (imm inst)) ie (rs1 @% "tag");
         RetE ((DefaultBaseFuncUnitsInput inst rs1 rs2)
                 @%[ "cap" <- #capIn ]
                 @%[ "xor" <- #xorIn ]
                 @%[ "rsh" <- #rshIn ]));
      outputXform ty (res : BaseFuncUnitsOutput @# ty) :=
        (LETC memAddr <- res @% "cap" @% "addr"   ;
         LETC memTag <- (unpackBaseFuncExtraInfo (res @% "rsh")) @% "tag";
         LETC memCap <- res @% "xor";
         LETC memCapPerms <- res @% "cap" @% "perms";
         LETE exception <- mkJustException (if accessTag then Clc else Clx) #memTag #memCap #memCapPerms
                             #memAddr (res @% "cap" @% "bounds?") $$false $$false $$false;
         RetE (mkLd (res @% "lsh") #memAddr $size $$accessTag $$signExt #memCapPerms #exception));
      instProperties := {| hasRs1 := true; hasRs2 := false; implicit := 0 |}
    |}.
  
  Definition mkStEntry (name: string) (funct3Val: word 3) (size: nat) (accessTag: bool) :=
    {|instName     := name;
      xlens        := if (size * 8) <=? 32 then [32; 64] else [64];
      extensions   := [Base];
      uniqId       := [fieldVal opcodeField ('b"01000");
                       fieldVal funct3Field funct3Val];
      inputXform ty pc inst rs1 rs2 ie :=
        (LETC capIn : CapInput <-
                        STRUCT { "addr"     ::= rs1 @% "val";
                                 "offset"   ::= SignExtendTruncLsb Xlen ({<funct7 inst, rdFixed inst>});
                                 "size"     ::= $size;
                                 "zeroLsb?" ::= $$false };
         LETC xorIn : XlenInput <-
                        STRUCT { "arg1" ::= (rs1 @% "cap");
                                 "arg2" ::= $0 };
         LETC rshIn : RightShiftInput <- packBaseFuncExtraInfo (isNotZero (imm inst)) ie (rs1 @% "tag");
         LETC lshIn : LeftShiftInput <- STRUCT { "inp" ::= rs2 @% "val";
                                                 "sht" ::= $0 };
         LETE rs2CapPerms <- getPerms capAccessors (rs2 @% "cap");
         LETC andIn : XlenInput <- packStDataTaggedLocal (rs2 @% "tag") (!(#rs2CapPerms @% "GL"));
         LETC addIn : XlenPlus1Input <- packDataTagCap (rs2 @% "tag") (rs2 @% "cap");
         RetE ((DefaultBaseFuncUnitsInput inst rs1 rs2)
                 @%[ "cap" <- #capIn ]
                 @%[ "xor" <- #xorIn ]
                 @%[ "rsh" <- #rshIn ]
                 @%[ "lsh" <- #lshIn ]
                 @%[ "and" <- #andIn ]
                 @%[ "add" <- #addIn ]));
      outputXform ty (res : BaseFuncUnitsOutput @# ty) :=
        (LETC memAddr <- res @% "cap" @% "addr"   ;
         LETC memTag <- (unpackBaseFuncExtraInfo (res @% "rsh")) @% "tag";
         LETC memCap <- res @% "xor";
         LETC memCapPerms <- res @% "cap" @% "perms";
         LETC stVal <- res @% "lsh";
         LETC stDataTagCap <- unpackDataTagCap (res @% "add");
         LETC stDataTag <- #stDataTagCap @% "fst";
         LETC stDataCap <- #stDataTagCap @% "snd";
         LETC stDataTaggedLocal <- unpackStDataTaggedLocal (res @% "and");
         LETE exception <- mkJustException (if accessTag then Csc else Csx) #memTag #memCap #memCapPerms
                             #memAddr (res @% "cap" @% "bounds?") $$false $$false #stDataTaggedLocal;
         RetE (mkSt #stVal #memAddr #stDataTag #stDataCap $size $$accessTag #exception));
      instProperties := {| hasRs1 := true; hasRs2 := true; implicit := 0 |}
    |}.
  
  Definition memEntries: list (InstEntry BaseFuncUnitsInput BaseFuncUnitsOutput) := [
      mkLdEntry "clb"  ('b"000") 1 true  false;
      mkLdEntry "clh"  ('b"001") 2 true  false;
      mkLdEntry "clw"  ('b"010") 4 true  false;
      mkLdEntry "clbu" ('b"100") 1 false false;
      mkLdEntry "clhu" ('b"100") 2 false false;
      mkLdEntry "clwu" ('b"110") 4 false false;
      mkLdEntry "clc"  ('b"011") 8 true  true;
      mkStEntry "csb"  ('b"000") 1 false;
      mkStEntry "csh"  ('b"001") 2 false;
      mkStEntry "csw"  ('b"010") 4 false;
      mkStEntry "csc"  ('b"011") 8 true].

  Definition mkCapCs1RdEntry (name: string) (rs2Val: word 5)
    (fn: forall ty, Bool @# ty -> Cap @# ty -> CapOutput @# ty -> Data ## ty):
    InstEntry BaseFuncUnitsInput BaseFuncUnitsOutput :=
    {|instName     := name;
      xlens        := [32; 64];
      extensions   := [Base];
      uniqId       := [fieldVal opcodeField ('b"10110");
                       fieldVal funct3Field ('b"000");
                       fieldVal funct7Field ('b"1111111");
                       fieldVal rs2FixedField rs2Val];
      inputXform ty pc inst rs1 rs2 ie :=
        (LETC xorIn <- STRUCT { "arg1" ::= rs1 @% "cap";
                                "arg2" ::= $0 };
         LETC rshIn : RightShiftInput <- packBaseFuncExtraInfo (isNotZero (imm inst)) ie (rs1 @% "tag");
         LETC capIn : CapInput <- STRUCT { "addr"     ::= rs1 @% "val";
                                           "offset"   ::= $0;
                                           "size"     ::= $0;
                                           "zeroLsb?" ::= $$false };
         RetE ((DefaultBaseFuncUnitsInput inst rs1 rs2)
                 @%[ "cap" <- #capIn]
                 @%[ "xor" <- #xorIn]
                 @%[ "rsh" <- #rshIn]));
      outputXform ty (res : BaseFuncUnitsOutput @# ty) :=
        (LETC cap <- res @% "xor";
         LETC tag <- (unpackBaseFuncExtraInfo (res @% "rsh")) @% "tag";
         LETE ret <- fn ty #tag #cap (res @% "cap");
         RetE (mkIntReg #ret #cap (res @% "cap" @% "addr")));
      instProperties := {| hasRs1 := true; hasRs2 := false; implicit := 0 |}
    |}.
  
  Definition capCs1RdEntries: list (InstEntry BaseFuncUnitsInput BaseFuncUnitsOutput) := [
      mkCapCs1RdEntry "cGetAddr" ('b"01111")
        (fun ty tag cap capOut => RetE (capOut @% "addr"));
      mkCapCs1RdEntry "cGetBase" ('b"00010")
        (fun ty tag cap capOut => RetE (capOut @% "base"));
      mkCapCs1RdEntry "cGetHigh" ('b"10111")
        (fun ty tag cap capOut => RetE cap);
      mkCapCs1RdEntry "cGetLen"  ('b"00011")
        (fun ty tag cap capOut => (LETC base <- capOut @% "base";
                                   LETC top <- capOut @% "top";
                                   LETC len <- #top - ZeroExtend 1 #base;
                                   LETC msbLen <- unpack Bool (UniBit (TruncMsb Xlen 1) #len);
                                   RetE ITE #msbLen $$(wones Xlen) (UniBit (TruncLsb Xlen 1) #len)));
      mkCapCs1RdEntry "cGetPerm" ('b"00000")
        (fun ty tag cap capOut => RetE (ZeroExtendTruncLsb Xlen (pack (capOut @% "perms"))));
      mkCapCs1RdEntry "cGetTag"  ('b"00100")
        (fun ty tag cap capOut => RetE (ZeroExtendTruncLsb Xlen (pack tag)));
      mkCapCs1RdEntry "cGetTop"  ('b"11000")
        (fun ty tag cap capOut => (LETC top <- capOut @% "top";
                                   LETC msbTop <- unpack Bool (UniBit (TruncMsb Xlen 1) #top);
                                   RetE ITE #msbTop $$(wones Xlen) (UniBit (TruncLsb Xlen 1) #top)));
      mkCapCs1RdEntry "cGetType" ('b"00001")
        (fun ty tag cap capOut => RetE (ZeroExtendTruncLsb Xlen (getCapOType capAccessors cap)))
    ].
      
  Definition mkCapCs1CdEntry (name: string) (rs2Val: word 5)
    (fn: forall ty, Bool @# ty -> Cap @# ty -> CapOutput @# ty -> FullCapWithTag ## ty):
    InstEntry BaseFuncUnitsInput BaseFuncUnitsOutput :=
    {|instName     := name;
      xlens        := [32; 64];
      extensions   := [Base];
      uniqId       := [fieldVal opcodeField ('b"10110");
                       fieldVal funct3Field ('b"000");
                       fieldVal funct7Field ('b"1111111");
                       fieldVal rs2FixedField rs2Val];
      inputXform ty pc inst rs1 rs2 ie :=
        (LETC xorIn <- STRUCT { "arg1" ::= rs1 @% "cap";
                                "arg2" ::= $0 };
         LETC rshIn : RightShiftInput <- packBaseFuncExtraInfo (isNotZero (imm inst)) ie (rs1 @% "tag");
         LETC capIn : CapInput <- STRUCT { "addr"     ::= rs1 @% "val";
                                           "offset"   ::= $0;
                                           "size"     ::= $0;
                                           "zeroLsb?" ::= $$false };
         RetE ((DefaultBaseFuncUnitsInput inst rs1 rs2)
                 @%[ "cap" <- #capIn]
                 @%[ "xor" <- #xorIn]
                 @%[ "rsh" <- #rshIn]));
      outputXform ty (res : BaseFuncUnitsOutput @# ty) :=
        (LETC cap <- res @% "xor";
         LETC tag <- (unpackBaseFuncExtraInfo (res @% "rsh")) @% "tag";
         LETE ret <- fn ty #tag #cap (res @% "cap");
         RetE (mkCapResult (#ret @% "val") (#ret @% "cap") (#ret @% "val") (#ret @% "tag")));
      instProperties := {| hasRs1 := true; hasRs2 := false; implicit := 0 |}
    |}.

  Definition capCs1CdEntries: list (InstEntry BaseFuncUnitsInput BaseFuncUnitsOutput) := [
      mkCapCs1CdEntry "cClearTag" ('b"01011") (fun ty tag cap capOut => RetE (STRUCT {
                                                                                  "tag" ::= $$false;
                                                                                  "cap" ::= cap;
                                                                                  "val" ::= capOut @% "addr"   
                                                                                } : FullCapWithTag @# ty));
      mkCapCs1CdEntry "cMove"     ('b"01010") (fun ty tag cap capOut => RetE (STRUCT {
                                                                                  "tag" ::= tag;
                                                                                  "cap" ::= cap;
                                                                                  "val" ::= capOut @% "addr"   
                                                                                } : FullCapWithTag @# ty))
    ].

  Definition mkCapCs1Rs2CdEntry (name: string) (funct7Val: word 7)
    (addrFn: forall ty, Addr @# ty -> Addr @# ty -> Addr @# ty)
    (offsetFn: forall ty, Addr @# ty -> Addr @# ty -> Addr @# ty)
    (fn: forall ty, Bool @# ty -> Cap @# ty -> CapOutput @# ty -> Data @# ty -> FullCapWithTag ## ty):
    InstEntry BaseFuncUnitsInput BaseFuncUnitsOutput :=
    {|instName     := name;
      xlens        := [32; 64];
      extensions   := [Base];
      uniqId       := [fieldVal opcodeField ('b"10110");
                       fieldVal funct3Field ('b"000");
                       fieldVal funct7Field funct7Val];
      inputXform ty pc inst rs1 rs2 ie :=
        (LETC xorIn <- STRUCT { "arg1" ::= rs1 @% "cap";
                                "arg2" ::= $0 };
         LETC rshIn : RightShiftInput <- packBaseFuncExtraInfo (isNotZero (imm inst)) ie (rs1 @% "tag");
         LETC capIn : CapInput <- STRUCT { "addr"     ::= addrFn ty (rs1 @% "val") (rs2 @% "val");
                                           "offset"   ::= offsetFn ty (rs1 @% "val") (rs2 @% "val");
                                           "size"     ::= $0;
                                           "zeroLsb?" ::= $$false };
         LETC lshIn : LeftShiftInput <- STRUCT { "inp" ::= rs2 @% "val";
                                                 "sht" ::= $0 };
         RetE ((DefaultBaseFuncUnitsInput inst rs1 rs2)
                 @%[ "cap" <- #capIn]
                 @%[ "xor" <- #xorIn]
                 @%[ "rsh" <- #rshIn]
                 @%[ "lsh" <- #lshIn]));
      outputXform ty (res : BaseFuncUnitsOutput @# ty) :=
        (LETC cap <- res @% "xor";
         LETC tag <- (unpackBaseFuncExtraInfo (res @% "rsh")) @% "tag";
         LETC val <- res @% "lsh";
         LETE ret <- fn ty #tag #cap (res @% "cap") #val;
         RetE (mkCapResult (#ret @% "val") (#ret @% "cap") (#ret @% "val") (#ret @% "tag")));
      instProperties := {| hasRs1 := true; hasRs2 := true; implicit := 0 |}
    |}.

  Definition capCs1Rs2CdEntries: list (InstEntry BaseFuncUnitsInput BaseFuncUnitsOutput) := [
      mkCapCs1Rs2CdEntry "cAndPerm" ('b"0001101") (fun ty rs1 _ => rs1) (fun ty _ _ => $0)
        (fun ty tag cap capOut rs2 =>
           (LETC perms <- capOut @% "perms";
            LETC mask <- ZeroExtendTruncLsb (size CapPerms) rs2;
            LETC andPerms <- unpack CapPerms (#mask .& (pack #perms));
            LETE newCap <- setPerms capAccessors cap #andPerms;
            RetE ((STRUCT { "tag" ::= tag && !isSealed capAccessors cap;
                            "cap" ::= #newCap;
                            "val" ::= capOut @% "addr" }) : FullCapWithTag @# ty)));
      mkCapCs1Rs2CdEntry "cIncAddr" ('b"001001") (fun ty rs1 _ => rs1) (fun ty _ rs2 => rs2)
        (fun ty tag cap capOut rs2 =>
           (RetE ((STRUCT { "tag" ::= tag && !isSealed capAccessors cap && capOut @% "bounds?";
                            "cap" ::= cap;
                            "val" ::= capOut @% "addr" }) : FullCapWithTag @# ty)));
      mkCapCs1Rs2CdEntry "cSetAddr" ('b"001001") (fun ty _ _ => $0) (fun ty _ rs2 => rs2)
        (fun ty tag cap capOut rs2 =>
           (RetE ((STRUCT { "tag" ::= tag && !isSealed capAccessors cap && capOut @% "bounds?";
                            "cap" ::= cap;
                            "val" ::= capOut @% "addr" }) : FullCapWithTag @# ty)));
      mkCapCs1Rs2CdEntry "cSetHigh" ('b"0010110") (fun ty rs1 _ => rs1) (fun ty _ _ => $0)
        (fun ty tag cap capOut rs2 =>
           (RetE ((STRUCT { "tag" ::= $$false;
                            "cap" ::= rs2;
                            "val" ::= capOut @% "addr" }) : FullCapWithTag @# ty)));
      mkCapCs1Rs2CdEntry "cSub"     ('b"0010100") (fun ty rs1 _ => rs1) (fun ty _ rs2 => neg rs2)
        (fun ty tag cap capOut rs2 =>
           (RetE ((STRUCT { "tag" ::= $$false;
                            "cap" ::= $0;
                            "val" ::= capOut @% "addr" }) : FullCapWithTag @# ty)))
    ].

  (* TODO:
     - Cs1Cs2Rd
       + CSetEqualExact := tag, cap and val should all match. Use xor and adder?
       + CTestSubset := both tags should be the same, cap of cs2 should be a subset of cs1 in permission and bounds.
                        Perms can be sent to "and" logic; tags sent somewhere for equality; bounds checked explicitly "somehow"
     - Cs1Cs2Cd
       + CSeal := new tag is set only if (cs1 is tagged, cs1 is unsealed, cs2 is tagged, cs2 is not sealed, cs2 permit seal, cs2 in bounds,
                                          if cs1.EX then 1 <= cs2.val <= 7 else 9 <= cs2_addr <= 15), 
       + CUnseal := new tag is set only if (cs1 is tagged, cs2 bounds check, cs2 permit unseal, cs2 not sealed, cs1 sealed and cs1.otype = cs2.val), new G = cs1.G && cs12.G
     - Rs1Rd
       + CRoundRepresentableLength := Needs "e", which is effectively countLeadingZeros of length
       + CRepresentableAlignmentMask := Needs "e" 
     - Cs1ImmCd
       + CIncAddrImm := increment address, clear tag if not in bounds
       + CSetBoundsImm
     - Cs1Rs2Cd
       + CSetBounds
       + CSetBoundsExact
   *)
  (* TODO: cap, extract common elements from adder, shifter and logical (actually not much to create common functions for) *)

  Definition baseFuncEntry : FuncEntry :=
    {|funcName := "base";
      func     := BaseFuncUnits;
      insts    := arithEntries ++ logicalEntries ++ shiftEntries ++ addressEntries ++
                    branchEntries ++ jalEntries ++ memEntries ++ getCapEntries ++ setCapEntries |}.
End Alu.

(*
capSetBounds (base, length) -> E, B, T, exact?
ePrelim = 23 - countLeadingZeros(TruncLsb 23 length)
eInit = if (ePrelim > 14) then 24 else ePrelim
EInit = if (ePrelim > 14) then 15 else ePrelim

*)
