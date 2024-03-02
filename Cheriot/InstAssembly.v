Require Import Kami.AllNotations ProcKami.Cheriot.Lib ProcKami.Cheriot.Assembly ProcKami.Cheriot.Types.

Require Import ProcKami.Cheriot.InstSpec ProcKami.Cheriot.CoreConfig.

Declare Scope cheriot_assembly_scope.
Delimit Scope cheriot_assembly_scope with cheriot_assembly.

Notation x0 := 0%Z.
Notation x1 := 1%Z.
Notation x2 := 2%Z.
Notation x3 := 3%Z.
Notation x4 := 4%Z.
Notation x5 := 5%Z.
Notation x6 := 6%Z.
Notation x7 := 7%Z.
Notation x8 := 8%Z.
Notation x9 := 9%Z.
Notation x10 := 10%Z.
Notation x11 := 11%Z.
Notation x12 := 12%Z.
Notation x13 := 13%Z.
Notation x14 := 14%Z.
Notation x15 := 15%Z.
Notation x16 := 16%Z.
Notation x17 := 17%Z.
Notation x18 := 18%Z.
Notation x19 := 19%Z.
Notation x20 := 20%Z.
Notation x21 := 21%Z.
Notation x22 := 22%Z.
Notation x23 := 23%Z.
Notation x24 := 24%Z.
Notation x25 := 25%Z.
Notation x26 := 26%Z.
Notation x27 := 27%Z.
Notation x28 := 28%Z.
Notation x29 := 29%Z.
Notation x30 := 30%Z.
Notation x31 := 31%Z.

Notation c0 := 0%Z.
Notation c1 := 1%Z.
Notation c2 := 2%Z.
Notation c3 := 3%Z.
Notation c4 := 4%Z.
Notation c5 := 5%Z.
Notation c6 := 6%Z.
Notation c7 := 7%Z.
Notation c8 := 8%Z.
Notation c9 := 9%Z.
Notation c10 := 10%Z.
Notation c11 := 11%Z.
Notation c12 := 12%Z.
Notation c13 := 13%Z.
Notation c14 := 14%Z.
Notation c15 := 15%Z.
Notation c16 := 16%Z.
Notation c17 := 17%Z.
Notation c18 := 18%Z.
Notation c19 := 19%Z.
Notation c20 := 20%Z.
Notation c21 := 21%Z.
Notation c22 := 22%Z.
Notation c23 := 23%Z.
Notation c24 := 24%Z.
Notation c25 := 25%Z.
Notation c26 := 26%Z.
Notation c27 := 27%Z.
Notation c28 := 28%Z.
Notation c29 := 29%Z.
Notation c30 := 30%Z.
Notation c31 := 31%Z.

Notation zero := 0%Z.
Notation ra := 1%Z.
Notation sp := 2%Z.
Notation gp := 3%Z.
Notation tp := 4%Z.
Notation t0 := 5%Z.
Notation t1 := 6%Z.
Notation t2 := 7%Z.
Notation s0 := 8%Z.
Notation fp := 8%Z.
Notation s1 := 9%Z.
Notation a0 := 10%Z.
Notation a1 := 11%Z.
Notation a2 := 12%Z.
Notation a3 := 13%Z.
Notation a4 := 14%Z.
Notation a5 := 15%Z.
Notation a6 := 16%Z.
Notation a7 := 17%Z.
Notation s2 := 18%Z.
Notation s3 := 19%Z.
Notation s4 := 20%Z.
Notation s5 := 21%Z.
Notation s6 := 22%Z.
Notation s7 := 23%Z.
Notation s8 := 24%Z.
Notation s9 := 25%Z.
Notation s10 := 26%Z.
Notation s11 := 27%Z.
Notation t3 := 28%Z.
Notation t4 := 29%Z.
Notation t5 := 30%Z.
Notation t6 := 31%Z.

Notation meprevpcc := 27%Z.
Notation mtcc := 28%Z.
Notation mtdc := 29%Z.
Notation mscratchc := 30%Z.
Notation mepcc := 31%Z.

Notation mstatus := (Z.of_N (hex "300")).
Notation mie := (Z.of_N (hex "304")).
Notation mcause := (Z.of_N (hex "342")).
Notation mtval := (Z.of_N (hex "343")).

Local Open Scope cheriot_assembly_scope.

Notation "'addi' pd , ps1 , pimm" := (ProgInst (Build_Instruction "AddI" ps1 x0 pd 0%Z pimm) false) (at level 65).
Notation "'slti' pd , ps1 , pimm" := (ProgInst (Build_Instruction "SLTI" ps1 x0 pd 0%Z pimm) false) (at level 65).
Notation "'sltiu' pd , ps1 , pimm" := (ProgInst (Build_Instruction "SLTIU" ps1 x0 pd 0%Z pimm) false) (at level 65).
Notation "'xori' pd , ps1 , pimm" := (ProgInst (Build_Instruction "XorI" ps1 x0 pd 0%Z pimm) false) (at level 65).
Notation "'ori' pd , ps1 , pimm" := (ProgInst (Build_Instruction "OrI" ps1 x0 pd 0%Z pimm) false) (at level 65).
Notation "'andi' pd , ps1 , pimm" := (ProgInst (Build_Instruction "AndI" ps1 x0 pd 0%Z pimm) false) (at level 65).
Notation "'slli' pd , ps1 , pimm" := (ProgInst (Build_Instruction "SLLI" ps1 x0 pd 0%Z pimm) false) (at level 65).
Notation "'srli' pd , ps1 , pimm" := (ProgInst (Build_Instruction "SRLI" ps1 x0 pd 0%Z pimm) false) (at level 65).
Notation "'srai' pd , ps1 , pimm" := (ProgInst (Build_Instruction "SRAI" ps1 x0 pd 0%Z pimm) false) (at level 65).

Notation "'add' pd , ps1 , ps2" := (ProgInst (Build_Instruction "Add" ps1 ps2 pd 0%Z 0%Z) false) (at level 65).
Notation "'sub' pd , ps1 , ps2" := (ProgInst (Build_Instruction "Sub" ps1 ps2 pd 0%Z 0%Z) false) (at level 65).
Notation "'slt' pd , ps1 , ps2" := (ProgInst (Build_Instruction "SLT" ps1 ps2 pd 0%Z 0%Z) false) (at level 65).
Notation "'sltu' pd , ps1 , ps2" := (ProgInst (Build_Instruction "SLTU" ps1 ps2 pd 0%Z 0%Z) false) (at level 65).
Notation "'xor' pd , ps1 , ps2" := (ProgInst (Build_Instruction "Xor" ps1 ps2 pd 0%Z 0%Z) false) (at level 65).
Notation "'or' pd , ps1 , ps2" := (ProgInst (Build_Instruction "Or" ps1 ps2 pd 0%Z 0%Z) false) (at level 65).
Notation "'and' pd , ps1 , ps2" := (ProgInst (Build_Instruction "And" ps1 ps2 pd 0%Z 0%Z) false) (at level 65).
Notation "'sll' pd , ps1 , ps2" := (ProgInst (Build_Instruction "SLL" ps1 ps2 pd 0%Z 0%Z) false) (at level 65).
Notation "'srl' pd , ps1 , ps2" := (ProgInst (Build_Instruction "SRL" ps1 ps2 pd 0%Z 0%Z) false) (at level 65).
Notation "'sra' pd , ps1 , ps2" := (ProgInst (Build_Instruction "SRA" ps1 ps2 pd 0%Z 0%Z) false) (at level 65).
Notation "'lui' pd , ps1 , ps2" := (ProgInst (Build_Instruction "LUI" ps1 ps2 pd 0%Z 0%Z) false) (at level 65).

Notation "'auicgp' pd , pimm" := (ProgInst (Build_Instruction "AUICGP" x0 x0 pd 0%Z pimm) false) (at level 65).
Notation "'auipcc' pd , pimm" := (ProgInst (Build_Instruction "AUIPCC" x0 x0 pd 0%Z pimm) false) (at level 65).
Notation "'candperm' pd , ps1 , ps2" := (ProgInst (Build_Instruction "CAndPerm" ps1 ps2 pd 0%Z 0%Z) false) (at level 65).
Notation "'ccleartag' pd , ps1" := (ProgInst (Build_Instruction "CClearTag" ps1 x0 pd 0%Z 0%Z) false) (at level 65).
Notation "'cgetaddr' pd , ps1" := (ProgInst (Build_Instruction "CGetAddr" ps1 x0 pd 0%Z 0%Z) false) (at level 65).
Notation "'cgetbase' pd , ps1" := (ProgInst (Build_Instruction "CGetBase" ps1 x0 pd 0%Z 0%Z) false) (at level 65).
Notation "'cgethigh' pd , ps1" := (ProgInst (Build_Instruction "CGetHigh" ps1 x0 pd 0%Z 0%Z) false) (at level 65).
Notation "'cgetlen' pd , ps1" := (ProgInst (Build_Instruction "CGetLen" ps1 x0 pd 0%Z 0%Z) false) (at level 65).
Notation "'cgetperm' pd , ps1" := (ProgInst (Build_Instruction "CGetPerm" ps1 x0 pd 0%Z 0%Z) false) (at level 65).
Notation "'cgettag' pd , ps1" := (ProgInst (Build_Instruction "CGetTag" ps1 x0 pd 0%Z 0%Z) false) (at level 65).
Notation "'cgettop' pd , ps1" := (ProgInst (Build_Instruction "CGetTop" ps1 x0 pd 0%Z 0%Z) false) (at level 65).
Notation "'cgettype' pd , ps1" := (ProgInst (Build_Instruction "CGetType" ps1 x0 pd 0%Z 0%Z) false) (at level 65).
Notation "'cincaddr' pd , ps1 , ps2" := (ProgInst (Build_Instruction "CIncAddr" ps1 ps2 pd 0%Z 0%Z) false) (at level 65).
Notation "'cincaddrimm' pd , ps1 , pimm" := (ProgInst (Build_Instruction "CIncAddrPimm" ps1 x0 pd 0%Z pimm) false) (at level 65).
Notation "'cmove' pd , ps1" := (ProgInst (Build_Instruction "CMove" ps1 x0 pd 0%Z 0%Z) false) (at level 65).
Notation "'cram' pd , ps1" := (ProgInst (Build_Instruction "CRepresentableAlignmentMask" ps1 x0 pd 0%Z 0%Z) false) (at level 65).
Notation "'crrl' pd , ps1" := (ProgInst (Build_Instruction "CRoundRepresentableLength" ps1 x0 pd 0%Z 0%Z) false) (at level 65).
Notation "'csetaddr' pd , ps1 , ps2" := (ProgInst (Build_Instruction "CSetAddr" ps1 ps2 pd 0%Z 0%Z) false) (at level 65).
Notation "'csetbounds' pd , ps1 , ps2" := (ProgInst (Build_Instruction "CSetBounds" ps1 ps2 pd 0%Z 0%Z) false) (at level 65).
Notation "'csetboundsexact' pd , ps1 , ps2" := (ProgInst (Build_Instruction "CSetBoundsExact" ps1 ps2 pd 0%Z 0%Z) false) (at level 65).
Notation "'csetboundsimm' pd , ps1 , pimm" := (ProgInst (Build_Instruction "CSetBoundsPimm" ps1 x0 pd 0%Z pimm) false) (at level 65).
Notation "'csetequalexact' pd , ps1 , ps2" := (ProgInst (Build_Instruction "CSetEqualExact" ps1 ps2 pd 0%Z 0%Z) false) (at level 65).
Notation "'csethigh' pd , ps1 , ps2" := (ProgInst (Build_Instruction "CSetHigh" ps1 ps2 pd 0%Z 0%Z) false) (at level 65).
Notation "'csub' pd , ps1 , ps2" := (ProgInst (Build_Instruction "CSub" ps1 ps2 pd 0%Z 0%Z) false) (at level 65).
Notation "'ctestsubset' pd , ps1 , ps2" := (ProgInst (Build_Instruction "CTestSubset" ps1 ps2 pd 0%Z 0%Z) false) (at level 65).
Notation "'cseal' pd , ps1 , ps2" := (ProgInst (Build_Instruction "CSeal" ps1 ps2 pd 0%Z 0%Z) false) (at level 65).
Notation "'cunseal' pd , ps1 , ps2" := (ProgInst (Build_Instruction "CUnseal" ps1 ps2 pd 0%Z 0%Z) false) (at level 65).

Notation "'beq' ps1 , ps2 , imm" := (ProgInst (Build_Instruction "BEq" ps1 ps2 x0 0%Z imm) true) (at level 65).
Notation "'bne' ps1 , ps2 , imm" := (ProgInst (Build_Instruction "BNE" ps1 ps2 x0 0%Z imm) true) (at level 65).
Notation "'blt' ps1 , ps2 , imm" := (ProgInst (Build_Instruction "BLT" ps1 ps2 x0 0%Z imm) true) (at level 65).
Notation "'bge' ps1 , ps2 , imm" := (ProgInst (Build_Instruction "BGE" ps1 ps2 x0 0%Z imm) true) (at level 65).
Notation "'bltu' ps1 , ps2 , imm" := (ProgInst (Build_Instruction "BLTU" ps1 ps2 x0 0%Z imm) true) (at level 65).
Notation "'bgeu' ps1 , ps2 , imm" := (ProgInst (Build_Instruction "BGEU" ps1 ps2 x0 0%Z imm) true) (at level 65).

Notation "'clb' pd , imm ( ps1 )" := (ProgInst (Build_Instruction "CLB" ps1 x0 pd 0%Z imm) false) (at level 65).
Notation "'clh' pd , imm ( ps1 )" := (ProgInst (Build_Instruction "CLh" ps1 x0 pd 0%Z imm) false) (at level 65).
Notation "'clw' pd , imm ( ps1 )" := (ProgInst (Build_Instruction "CLw" ps1 x0 pd 0%Z imm) false) (at level 65).
Notation "'clbu' pd , imm ( ps1 )" := (ProgInst (Build_Instruction "CLBU" ps1 x0 pd 0%Z imm) false) (at level 65).
Notation "'clhu' pd , imm ( ps1 )" := (ProgInst (Build_Instruction "CLHU" ps1 x0 pd 0%Z imm) false) (at level 65).
Notation "'clc' pd , imm ( ps1 )" := (ProgInst (Build_Instruction "CLC" ps1 x0 pd 0%Z imm) false) (at level 65).

Notation "'csb' imm ( ps1 ), ps2" := (ProgInst (Build_Instruction "CLB" ps1 ps2 x0 0%Z imm) false) (at level 65).
Notation "'csh' imm ( ps1 ), ps2" := (ProgInst (Build_Instruction "CLH" ps1 ps2 x0 0%Z imm) false) (at level 65).
Notation "'csw' imm ( ps1 ), ps2" := (ProgInst (Build_Instruction "CLW" ps1 ps2 x0 0%Z imm) false) (at level 65).
Notation "'csc' imm ( ps1 ), ps2" := (ProgInst (Build_Instruction "CLC" ps1 ps2 x0 0%Z imm) false) (at level 65).

Notation "'cjal' pd , imm" := (ProgInst (Build_Instruction "CJAL" x0 x0 pd 0%Z imm) true) (at level 65).
Notation "'cj' imm" := (ProgInst (Build_Instruction "CJAL" x0 x0 x0 0%Z imm) true) (at level 65).

Notation "'cjalr' pd , ps1" := (ProgInst (Build_Instruction "CJALR" ps1 x0 pd 0%Z 0%Z) false) (at level 65).
Notation "'cjr' ps1" := (ProgInst (Build_Instruction "CJALR" ps1 x0 x0 0%Z 0%Z) false) (at level 65).

Notation "'ecall'" := (ProgInst (Build_Instruction "ECall" x0 x0 x0 0%Z 0%Z) false) (at level 65).
Notation "'mret'" := (ProgInst (Build_Instruction "MRet" x0 x0 x0 0%Z 0%Z) false) (at level 65).
Notation "'fence.i'" := (ProgInst (Build_Instruction "FenceI" x0 x0 x0 0%Z 0%Z) false) (at level 65).

Notation "'csrrw' pd , csrId , ps1" := (ProgInst (Build_Instruction "CSRRW" ps1 x0 pd csrId 0%Z) false) (at level 65).
Notation "'csrrs' pd , csrId , ps1" := (ProgInst (Build_Instruction "CSRRS" ps1 x0 pd csrId 0%Z) false) (at level 65).
Notation "'csrrc' pd , csrId , ps1" := (ProgInst (Build_Instruction "CSRRC" ps1 x0 pd csrId 0%Z) false) (at level 65).

Notation "'csrw' csrId , ps1" := (ProgInst (Build_Instruction "CSRRW" ps1 x0 x0 csrId 0%Z) false) (at level 65).
Notation "'csrs' csrId , ps1" := (ProgInst (Build_Instruction "CSRRS" ps1 x0 x0 csrId 0%Z) false) (at level 65).
Notation "'csrc' csrId , ps1" := (ProgInst (Build_Instruction "CSRRC" ps1 x0 x0 csrId 0%Z) false) (at level 65).

Notation "'csrr' pd , csrId" := (ProgInst (Build_Instruction "CSRRW" x0 x0 pd csrId 0%Z) false) (at level 65).

Notation "'csrrwi' pd , csrId , imm" := (ProgInst (Build_Instruction "CSRRWI" x0 x0 pd csrId imm) false) (at level 65).
Notation "'csrrsi' pd , csrId , imm" := (ProgInst (Build_Instruction "CSRRSI" x0 x0 pd csrId imm) false) (at level 65).
Notation "'csrrci' pd , csrId , imm" := (ProgInst (Build_Instruction "CSRRCI" x0 x0 pd csrId imm) false) (at level 65).

Notation "'csrwi' csrId , imm" := (ProgInst (Build_Instruction "CSRRWI" x0 x0 x0 csrId imm) false) (at level 65).
Notation "'csrsi' csrId , imm" := (ProgInst (Build_Instruction "CSRRSI" x0 x0 x0 csrId imm) false) (at level 65).
Notation "'csrci' csrId , imm" := (ProgInst (Build_Instruction "CSRRCI" x0 x0 x0 csrId imm) false) (at level 65).

Notation "'cspecialrw' pd , scrId , ps1" := (ProgInst (Build_Instruction "CSpecialRW" ps1 x0 pd scrId 0%Z) false) (at level 65).
Notation "'cspecialr' pd , scrId" := (ProgInst (Build_Instruction "CSpecialR" x0 x0 pd scrId 0%Z) false) (at level 65).
Notation "'cspecialw' scrId , ps1" := (ProgInst (Build_Instruction "CSpecialRW" ps1 x0 x0 scrId 0%Z) false) (at level 65).

Local Close Scope cheriot_assembly_scope.

Definition splitInst (w: word InstSz): list (word 8) :=
  [truncLsb w; truncLsb (@truncMsb 24 _ w); truncLsb (@truncMsb 16 _ w); truncMsb w].

Definition splitCompInst (w: word CompInstSz): list (word 8) :=
  [truncLsb w; truncMsb w].

Section Enc.
  Context `{coreConfigParams: CoreConfigParams}.

  Definition isNonNegZ (z : Z) := match z with
                                  | Z.neg _ => false
                                  | _ => true
                                  end.

  Definition NumRegId := Z.pow 2 (Z.of_nat (@RegIdSz procParams)).
  Definition NumRegIdFixed := Z.pow 2 (Z.of_nat RegFixedIdSz).

  Section z.
    Variable z: Z.
    Local Definition zWithinWidth (pow2PredWidth: Z) := Z.geb z (- pow2PredWidth)%Z && Z.ltb z pow2PredWidth.

    Local Definition zStart0Bits (start: nat) := Z.eqb (Z.modulo (Z.pow 2 (Z.of_nat start)) z) 0%Z.

    Local Definition zWithinWidthStart (start width: nat) := zStart0Bits start &&
                                                               zWithinWidth (Z.pow 2 (Z.of_nat (width - 1))).
  End z.

  Definition instAssemblyEnc (i: Instruction) : (list (word 8) + AssemblyError) :=
    let '(Build_Instruction name cs1I cs2I cdI csrI immI) := i in
    let findFu fu := find (fun ie => String.eqb (instName ie) name) (insts fu) in
    match find (fun fu => match findFu fu with
                          | Some _ => true
                          | None => false
                          end) specFuncUnits with
    | Some fu => match findFu fu with
                 | Some ie =>
                     let ip := @instProperties procParams _ ie in
                     if isNonNegZ cs1I &&  Z.ltb cs1I NumRegId
                     then if isNonNegZ cs2I && Z.ltb cs2I (if hasScr ip
                                                           then NumRegIdFixed
                                                           else NumRegId)
                          then if isNonNegZ cdI && Z.ltb cdI NumRegId
                               then if isNonNegZ csrI && Z.ltb csrI (Z.pow 2 12)
                                    then if (isNonNegZ immI || signExt ip) &&
                                              zWithinWidthStart immI (immStart ie) (immEnd ie)
                                         then inl (splitInst (encodeInst ie
                                                                (ZToWord _ cs1I) (ZToWord _ cs2I) (ZToWord _ cdI)
                                                                (ZToWord _ csrI) (ZToWord _ immI)))
                                         else inr Imm
                                    else inr Csr
                               else inr Cd
                          else inr Cs2
                     else inr Cs1
                 | None => inr InstAsmName
                 end
    | None => inr InstAsmName
    end.
End Enc.
