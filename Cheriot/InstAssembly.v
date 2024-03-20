Require Import Kami.AllNotations ProcKami.Cheriot.Lib ProcKami.Cheriot.Assembly ProcKami.Cheriot.Types.

Require Import ProcKami.Cheriot.InstSpec ProcKami.Cheriot.CoreConfig.

Declare Scope cheriot_assembly_scope.
Delimit Scope cheriot_assembly_scope with cheriot_assembly.

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

  Definition NumRegId := Z.pow 2 (Z.of_nat RegIdSz).
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
                     let ip := instProperties ie in
                     if (isNonNegZ immI || signExt ip) &&
                          zWithinWidthStart immI (immStart ie) (immEnd ie)
                     then inl (splitInst (encodeInst ie (getRegScrId cs1I) (getRegScrId cs2I) (getRegScrId cdI) (getCsrId csrI) (ZToWord _ immI)))
                     else inr Imm
                 | None => inr InstAsmName
                 end
    | None => inr InstAsmName
    end.
End Enc.
