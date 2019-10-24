Require Import Kami.AllNotations ProcKami.FU.
Require Import ProcKami.RiscvIsaSpec.Insts.Mem.MemFuncs.
Require Import List.
Import ListNotations.

Section Mem.
  Context `{procParams: ProcParams}.

  Section Ty.
    Variable ty: Kind -> Type.

    Local Open Scope kami_expr.

    Definition Amo64: FUEntry :=
      {| fuName := "amo64" ;
         fuFunc := (fun ty i => LETE x: MemInputAddrType <- i;
                               LETC addr : VAddr <- (#x @% "base") + (#x @% "offset") ;
                               LETC ret: MemOutputAddrType
                                           <-
                                           STRUCT {
                                             "addr" ::= #addr ;
                                             "data" ::= #x @% "data" ;
                                             "aq" ::= #x @% "aq" ;
                                             "rl" ::= #x @% "rl" ;
                                             "misalignedException?" ::=
                                               !(checkAligned #addr (#x @% "numZeros"))
                                           } ;
                               RetE #ret ) ;
         fuInsts :=
           {| instName     := "amoswap.d" ;
              xlens        :=  [Xlen64];
              extensions   := ["I"];
              ext_ctxt_off := nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"011") ::
                                       fieldVal funct5Field ('b"00001") :: nil ;
              inputXform   := fun ty => amoInput 3 (ty := ty);
              outputXform  := fun ty => amoTag (ty := ty) ;
              optMemParams := Some {| accessSize := 3; memXform := AmoEntry (fun ty reg mem => reg) |};
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
           |} ::
           {| instName     := "amoadd.d" ;
              xlens        :=  [Xlen64];
              extensions   := ["I"];
              ext_ctxt_off := nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"011") ::
                                       fieldVal funct5Field ('b"00000") :: nil ;
              inputXform   := fun ty => amoInput 3 (ty := ty);
              outputXform  := fun ty => amoTag (ty := ty) ;
              optMemParams := Some {| accessSize := 3; memXform := AmoEntry (fun ty reg mem => reg + mem) |};
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
           |} ::
           {| instName     := "amoxor.d" ;
              xlens        :=  [Xlen64];
              extensions   := ["I"];
              ext_ctxt_off := nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"011") ::
                                       fieldVal funct5Field ('b"00100") :: nil ;
              inputXform   := fun ty => amoInput 3 (ty := ty);
              outputXform  := fun ty => amoTag (ty := ty) ;
              optMemParams := Some {| accessSize := 3; memXform := AmoEntry (fun ty reg mem => reg ^ mem) |};
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
           |} ::
           {| instName     := "amoand.d" ;
              xlens        :=  [Xlen64];
              extensions   := ["I"];
              ext_ctxt_off := nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"011") ::
                                       fieldVal funct5Field ('b"01100") :: nil ;
              inputXform   := fun ty => amoInput 3 (ty := ty);
              outputXform  := fun ty => amoTag (ty := ty) ;
              optMemParams := Some {| accessSize := 3; memXform := AmoEntry (fun ty reg mem => (reg & mem)%kami_expr) |};
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
           |} ::
           {| instName     := "amoor.d" ;
              xlens        :=  [Xlen64];
              extensions   := ["I"];
              ext_ctxt_off := nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"011") ::
                                       fieldVal funct5Field ('b"01000") :: nil ;
              inputXform   := fun ty => amoInput 3 (ty := ty);
              outputXform  := fun ty => amoTag (ty := ty) ;
              optMemParams := Some {| accessSize := 3; memXform := AmoEntry (fun ty reg mem => (reg | mem)%kami_expr) |};
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
           |} ::
           {| instName     := "amomin.d" ;
              xlens        :=  [Xlen64];
              extensions   := ["I"];
              ext_ctxt_off := nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"011") ::
                                       fieldVal funct5Field ('b"10000") :: nil ;
              inputXform   := fun ty => amoInput 3 (ty := ty);
              outputXform  := fun ty => amoTag (ty := ty) ;
              optMemParams := Some {| accessSize := 3; memXform := AmoEntry (fun ty reg mem => IF (SignExtendTruncLsb 64 reg) >s (SignExtendTruncLsb (63+1) mem) then mem else reg) |};
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
           |} ::
           {| instName     := "amomax.d" ;
              xlens        :=  [Xlen64];
              extensions   := ["I"];
              ext_ctxt_off := nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"011") ::
                                       fieldVal funct5Field ('b"10100") :: nil ;
              inputXform   := fun ty => amoInput 3 (ty := ty);
              outputXform  := fun ty => amoTag (ty := ty) ;
              optMemParams := Some {| accessSize := 3; memXform := AmoEntry (fun ty reg mem => IF (SignExtendTruncLsb 64 reg) >s (SignExtendTruncLsb (63+1) mem) then reg else mem) |};
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
           |} ::
           {| instName     := "amominu.d" ;
              xlens        :=  [Xlen64];
              extensions   := ["I"];
              ext_ctxt_off := nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"011") ::
                                       fieldVal funct5Field ('b"11000") :: nil ;
              inputXform   := fun ty => amoInput 3 (ty := ty);
              outputXform  := fun ty => amoTag (ty := ty) ;
              optMemParams := Some {| accessSize := 3; memXform := AmoEntry (fun ty reg mem => IF (ZeroExtendTruncLsb 64 reg) > (ZeroExtendTruncLsb 64 mem) then mem else reg) |};
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
           |} ::
           {| instName     := "amomaxu.d" ;
              xlens        :=  [Xlen64];
              extensions   := ["I"];
              ext_ctxt_off := nil;
              uniqId       := fieldVal instSizeField ('b"11") ::
                                       fieldVal opcodeField ('b"01011") ::
                                       fieldVal funct3Field ('b"011") ::
                                       fieldVal funct5Field ('b"11100") :: nil ;
              inputXform   := fun ty => amoInput 3 (ty := ty);
              outputXform  := fun ty => amoTag (ty := ty) ;
              optMemParams := Some {| accessSize := 3; memXform := AmoEntry (fun ty reg mem => IF (ZeroExtendTruncLsb 64 reg) > (ZeroExtendTruncLsb 64 mem) then reg else mem) |};
              instHints    := falseHints<|hasRs1 := true|><|hasRs2 := true|><|hasRd := true|><|writeMem := true|>
           |} ::
           nil |}.

    Local Close Scope kami_expr.
  End Ty.
End Mem.
