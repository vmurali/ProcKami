Require Import Kami.AllNotations ProcKami.Cheriot.Lib ProcKami.Cheriot.Types.

Require Import ProcKami.Cheriot.InstSpec ProcKami.Cheriot.CoreConfig.

Record Instruction := {
    instEntry : InstEntrySpec;
    cs1       : RegName;
    cs2       : RegName;
    cd        : RegName;
    scr       : ScrName;
    csr       : CsrName;
    immVal    : Z }.

Definition getInstructionRel (inst: Instruction) (curr: Z) (immRel: bool) :=
  match immRel with
  | false => inst
  | true => let '(Build_Instruction ie cs1Idx cs2Idx cdIdx scrIdx csrIdx immV) := inst in
            Build_Instruction ie cs1Idx cs2Idx cdIdx scrIdx csrIdx (immV - curr)%Z
  end.

Inductive Prog :=
| ProgSkip
| ProgInst (inst: Instruction) (immRel: bool)
| ProgSeq (p1 p2: Prog)
| ProgDeclLabel (cont: Z -> Prog)
| ProgLabel (label: Z)
| ProgData (size: Z) (val: list (word 8))
| ProgAlign (size: Z).

Inductive ResolvedProg :=
| ResolvedProgSkip
| ResolvedProgInst (inst: Instruction) (immRel: bool)
| ResolvedProgSeq (p1 p2: ResolvedProg)
| ResolvedProgData (size: Z) (val: list (word 8))
| ResolvedProgAlign (size: Z).

Definition findInstEntry name : option InstEntrySpec :=
  find (fun x => String.eqb name (instName x)) specInstEntries.

Ltac findInstEntryLtac name :=
  let x := eval cbv [findInstEntry find String.eqb Ascii.eqb Bool.eqb instName
                       specInstEntries mkBranchInst mkLdInst mkStInst
             scrList isValidScrs legalizeScrs csrList isValidCsrs mkCsrEntry]
  in (findInstEntry name)
    in match x with
       | Some ?y => exact (y: InstEntrySpec)
       end.

Definition splitWord n (w: word n) k :=
  let numWords := (n + k - 1)/k in
  let a := @truncLsb (numWords * k) _ w in
  let arr := evalExpr (unpack (Array numWords (Bit k)) (Const type a)) in
  convertToList arr.

Definition splitInst (w: word InstSz): list (word 8) :=
  [truncLsb w; truncLsb (@truncMsb 24 _ w); truncLsb (@truncMsb 16 _ w); truncMsb w].

Definition splitCompInst (w: word CompInstSz): list (word 8) :=
  [truncLsb w; truncMsb w].

Definition instEncoder (i: Instruction) : list (word 8) :=
  let '(Build_Instruction ie cs1I cs2I cdI scrI csrI immI) := i in
  splitInst (encodeInst ie (getRegId cs1I) (getRegId cs2I) (getRegId cdI)
               (getScrId scrI) (getCsrId csrI) (ZToWord _ immI)).

Definition startAlign := 2%Z.

Definition instSize (inst: Instruction) := Z.of_nat (length (instEncoder inst)).

Definition getNextAlignDiff (sz curr: Z) :=
  let realCurr := Z.modulo (Z.pow 2 startAlign + curr) sz in
  (Z.modulo (sz - realCurr) sz)%Z.

Fixpoint getAddrMap (prog: Prog) (currLabelAddrMap: Z * Z * (Z -> Z)): Z * Z * (Z -> Z) :=
  match prog with
  | ProgSkip => currLabelAddrMap
  | ProgInst inst rel => let '(curr, label, addrMap) := currLabelAddrMap in
                         (curr + instSize inst, label, addrMap)%Z
  | ProgSeq p1 p2 => getAddrMap p2 (getAddrMap p1 currLabelAddrMap)
  | ProgDeclLabel cont => let '(curr, label, addrMap) := currLabelAddrMap in
                          getAddrMap (cont (label + 1)%Z) (curr, label + 1, addrMap)%Z
  | ProgLabel l => let '(curr, label, addrMap) := currLabelAddrMap in
                   (curr, label, fun i => if (i =? l)%Z
                                          then curr
                                          else addrMap i)
  | ProgData sz _ => let '(curr, label, addrMap) := currLabelAddrMap in
                     (curr + sz, label, addrMap)%Z
  | ProgAlign sz => let '(curr, label, addrMap) := currLabelAddrMap in
                    (curr + getNextAlignDiff sz curr, label, addrMap)%Z
  end.

Section setLabel.
  Variable addrMap: Z -> Z.
  Fixpoint setLabel (prog: Prog) (label: Z): ResolvedProg * Z :=
    match prog with
    | ProgSkip => (ResolvedProgSkip, label)
    | ProgInst inst rel => (ResolvedProgInst inst rel, label)
    | ProgSeq p1 p2 => let '(p1', l2) := setLabel p1 label in
                       let '(p2', l) := setLabel p2 l2 in
                       (ResolvedProgSeq p1' p2', l)
    | ProgDeclLabel cont => setLabel (cont (label + 1)%Z) (label + 1)%Z
    | ProgLabel l => (ResolvedProgData 0 [], (addrMap l))
    | ProgData sz data => (ResolvedProgData sz data, label)
    | ProgAlign sz => (ResolvedProgAlign sz, label)
    end.
End setLabel.

Fixpoint getInstBytesResolved (prog: ResolvedProg) (curr: Z): (list (word 8) * Z) :=
  match prog with
  | ResolvedProgSkip => ([], curr)
  | ResolvedProgInst inst immRel =>
      let instBytes := instEncoder (getInstructionRel inst curr immRel) in
      (instBytes, (curr + Z.of_nat (length instBytes))%Z)
  | ResolvedProgSeq p1 p2 => let '(p1', curr2) := getInstBytesResolved p1 curr in
                             let '(p2', c) := getInstBytesResolved p2 curr2 in
                             (p1' ++ p2', c)
  | ResolvedProgData size vals => (firstn (Z.to_nat size) vals, (curr + size)%Z)
  | ResolvedProgAlign size =>
      let len := getNextAlignDiff size curr in
      (repeat (wzero 8) (Z.to_nat len), (curr + len)%Z)
  end.

(* Bytes of instruction or the first error with assembly instruction, whether it's relative or not and a line number *)
Definition getInstBytes (prog: Prog): (list (word 8))%type :=
  let '(_, _, addrMap) := getAddrMap prog (0%Z, 0%Z, fun i => (-1)%Z) in
  let '(resolved, _) := setLabel addrMap prog 0%Z in
  let '(xs, _) := getInstBytesResolved resolved 0%Z in
  xs.

Definition isNonNegZ (z : Z) := match z with
                                | Z.neg _ => false
                                | _ => true
                                end.

Section z.
  Variable z: Z.
  Local Definition zWithinWidthSigned (width: nat) :=
    let pow2PredWidth := Z.pow 2 (Z.of_nat (width - 1)) in
    Z.geb z (- pow2PredWidth)%Z && Z.ltb z pow2PredWidth.

  Local Definition zWithinWidthUnsigned (width: nat) :=
    let pow2Width := Z.pow 2 (Z.of_nat width) in
    isNonNegZ z && Z.ltb z pow2Width.

  Local Definition zStart0Bits (start: nat) := Z.eqb (Z.modulo z (Z.pow 2 (Z.of_nat start))) 0%Z.

  Local Definition zWithinWidthStart (start width: nat) (signed: bool) :=
    zStart0Bits start && if signed
                         then zWithinWidthSigned width
                         else zWithinWidthUnsigned width.
End z.

Definition isImmValid (i: Instruction) :=
  let '(Build_Instruction ie cs1I cs2I cdI scrI csrI immI) := i in
  zWithinWidthStart immI (immStart ie) (immEnd ie) (signExt (instProperties ie)).

(* TODO: Use length instBytes when compressed is supported *)
Fixpoint getInstBytesErrorResolved (prog: ResolvedProg) (curr: Z) (idx: nat):
  (Z * nat * list (Instruction * bool * Z * nat)) :=
  match prog with
  | ResolvedProgSkip => (curr, S idx, [])
  | ResolvedProgInst inst immRel =>
      ((curr + 4)%Z, S idx,
        if isImmValid (getInstructionRel inst curr immRel) then [] else [(inst, immRel, curr, idx)])
  | ResolvedProgSeq p1 p2 => let '(curr2, i2, errs1) := getInstBytesErrorResolved p1 curr idx in
                             let '(c, i, errs2) := getInstBytesErrorResolved p2 curr2 i2 in
                             (c, i, errs1 ++ errs2)
  | ResolvedProgData size vals => ((curr + size)%Z, S idx, [])
  | ResolvedProgAlign size =>
      let len := getNextAlignDiff size curr in
      ((curr + len)%Z, S idx, [])
  end.

Definition getInstBytesError (prog: Prog): list (Instruction * bool * Z * nat) :=
  let '(_, _, addrMap) := getAddrMap prog (0%Z, 0%Z, fun i => (-1)%Z) in
  let '(resolved, _) := setLabel addrMap prog 0%Z in
  let '(_, _, errs) := getInstBytesErrorResolved resolved 0%Z 0 in
  errs.

Declare Scope cheriot_assembly_scope.
Delimit Scope cheriot_assembly_scope with cheriot_assembly.

Local Notation BuildInst name ps1 ps2 pd scrId csrId immV rel :=
  (ProgInst (Build_Instruction ltac:(findInstEntryLtac name) ps1 ps2 pd scrId csrId immV%Z) rel)
    (only parsing).

Local Open Scope cheriot_assembly_scope.

Notation "p1 ;; p2" := (ProgSeq p1 p2) (at level 65, right associativity): cheriot_assembly_scope.
Notation "'LOCAL' l ';' p" := (ProgDeclLabel (fun l => p)) (at level 65, l ident, right associativity): cheriot_assembly_scope.
Notation "l ':;'" := (ProgLabel l) (at level 8, no associativity, format "l ':;'"): cheriot_assembly_scope.
Notation "l ':;;' p" := (ProgSeq (ProgLabel l) p) (at level 8, p at level 65, right associativity, format "l ':;;' p"): cheriot_assembly_scope.
Notation "'.align' sz" := (ProgAlign sz%Z) (at level 65): cheriot_assembly_scope.
Notation "'.byte' val" := (ProgData 1%Z [ZToWord 8 val]) (at level 65): cheriot_assembly_scope.
Notation "'.hword' val" := (ProgData 2%Z [ZToWord 8 val; ZToWord 8 (val/(Z.pow 2 8))]) (at level 65): cheriot_assembly_scope.
Notation "'.word' val" := (ProgData 4%Z [ZToWord 8 val; ZToWord 8 (val/(Z.pow 2 8)); ZToWord 8 (val/(Z.pow 2 16)); ZToWord 8 (val/(Z.pow 2 24))]) (at level 65): cheriot_assembly_scope.
Notation "'.dword' val" :=
  (ProgData 4%Z [ZToWord 8 val; ZToWord 8 (val/(Z.pow 2 8)); ZToWord 8 (val/(Z.pow 2 16)); ZToWord 8 (val/(Z.pow 2 24));
                 ZToWord 8 (val/(Z.pow 2 32)); ZToWord 8 (val/(Z.pow 2 40)); ZToWord 8 (val/(Z.pow 2 48)); ZToWord 8 (val/(Z.pow 2 56))]) (at level 65): cheriot_assembly_scope.

Notation "'addi' pd , ps1 , pimm" := (BuildInst "AddI" ps1 x0 pd scr0 csr0 pimm%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'slti' pd , ps1 , pimm" := (BuildInst "SLTI" ps1 x0 pd scr0 csr0 pimm%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'sltiu' pd , ps1 , pimm" := (BuildInst "SLTIU" ps1 x0 pd scr0 csr0 pimm%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'xori' pd , ps1 , pimm" := (BuildInst "XorI" ps1 x0 pd scr0 csr0 pimm%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'ori' pd , ps1 , pimm" := (BuildInst "OrI" ps1 x0 pd scr0 csr0 pimm%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'andi' pd , ps1 , pimm" := (BuildInst "AndI" ps1 x0 pd scr0 csr0 pimm%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'slli' pd , ps1 , pimm" := (BuildInst "SLLI" ps1 x0 pd scr0 csr0 pimm%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'srli' pd , ps1 , pimm" := (BuildInst "SRLI" ps1 x0 pd scr0 csr0 pimm%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'srai' pd , ps1 , pimm" := (BuildInst "SRAI" ps1 x0 pd scr0 csr0 pimm%Z false) (at level 65, only parsing): cheriot_assembly_scope.

Notation "'add' pd , ps1 , ps2" := (BuildInst "Add" ps1 ps2 pd scr0 csr0 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'sub' pd , ps1 , ps2" := (BuildInst "Sub" ps1 ps2 pd scr0 csr0 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'slt' pd , ps1 , ps2" := (BuildInst "SLT" ps1 ps2 pd scr0 csr0 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'sltu' pd , ps1 , ps2" := (BuildInst "SLTU" ps1 ps2 pd scr0 csr0 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'xor' pd , ps1 , ps2" := (BuildInst "Xor" ps1 ps2 pd scr0 csr0 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'or' pd , ps1 , ps2" := (BuildInst "Or" ps1 ps2 pd scr0 csr0 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'and' pd , ps1 , ps2" := (BuildInst "And" ps1 ps2 pd scr0 csr0 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'sll' pd , ps1 , ps2" := (BuildInst "SLL" ps1 ps2 pd scr0 csr0 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'srl' pd , ps1 , ps2" := (BuildInst "SRL" ps1 ps2 pd scr0 csr0 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'sra' pd , ps1 , ps2" := (BuildInst "SRA" ps1 ps2 pd scr0 csr0 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'lui' pd , pimm" := (BuildInst "LUI" x0 x0 pd scr0 csr0 (Z.shiftr pimm 12%Z) false) (at level 65, only parsing): cheriot_assembly_scope.

Notation "'%hi(' pimm )" := (Z.shiftr pimm%Z 12%Z) (at level 64): cheriot_assembly_scope.
Notation "'%lo(' pimm )" := (Z.modulo pimm%Z (Z.pow 2 12)) (at level 64): cheriot_assembly_scope.

Notation "'auicgp' pd , pimm" := (BuildInst "AUICGP" x0 x0 pd scr0 csr0 pimm%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'auipcc' pd , pimm" := (BuildInst "AUIPCC" x0 x0 pd scr0 csr0 pimm%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'candperm' pd , ps1 , ps2" := (BuildInst "CAndPerm" ps1 ps2 pd scr0 csr0 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'ccleartag' pd , ps1" := (BuildInst "CClearTag" ps1 x0 pd scr0 csr0 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'cgetaddr' pd , ps1" := (BuildInst "CGetAddr" ps1 x0 pd scr0 csr0 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'cgetbase' pd , ps1" := (BuildInst "CGetBase" ps1 x0 pd scr0 csr0 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'cgethigh' pd , ps1" := (BuildInst "CGetHigh" ps1 x0 pd scr0 csr0 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'cgetlen' pd , ps1" := (BuildInst "CGetLen" ps1 x0 pd scr0 csr0 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'cgetperm' pd , ps1" := (BuildInst "CGetPerm" ps1 x0 pd scr0 csr0 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'cgettag' pd , ps1" := (BuildInst "CGetTag" ps1 x0 pd scr0 csr0 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'cgettop' pd , ps1" := (BuildInst "CGetTop" ps1 x0 pd scr0 csr0 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'cgettype' pd , ps1" := (BuildInst "CGetType" ps1 x0 pd scr0 csr0 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'cincaddr' pd , ps1 , ps2" := (BuildInst "CIncAddr" ps1 ps2 pd scr0 csr0 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'cincaddrimm' pd , ps1 , pimm" := (BuildInst "CIncAddrImm" ps1 x0 pd scr0 csr0 pimm%Z false)
                                              (at level 65, only parsing): cheriot_assembly_scope.
Notation "'cmove' pd , ps1" := (BuildInst "CMove" ps1 x0 pd scr0 csr0 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'cram' pd , ps1" := (BuildInst "CRAM" ps1 x0 pd scr0 csr0 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'crrl' pd , ps1" := (BuildInst "CRRL" ps1 x0 pd scr0 csr0 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'csetaddr' pd , ps1 , ps2" := (BuildInst "CSetAddr" ps1 ps2 pd scr0 csr0 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'csetbounds' pd , ps1 , ps2" := (BuildInst "CSetBounds" ps1 ps2 pd scr0 csr0 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'csetboundsexact' pd , ps1 , ps2" := (BuildInst "CSetBoundsExact" ps1 ps2 pd scr0 csr0 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'csetboundsimm' pd , ps1 , pimm" := (BuildInst "CSetBoundsImm" ps1 x0 pd scr0 csr0 pimm%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'csetequalexact' pd , ps1 , ps2" := (BuildInst "CSetEqualExact" ps1 ps2 pd scr0 csr0 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'csethigh' pd , ps1 , ps2" := (BuildInst "CSetHigh" ps1 ps2 pd scr0 csr0 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'csub' pd , ps1 , ps2" := (BuildInst "CSub" ps1 ps2 pd scr0 csr0 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'ctestsubset' pd , ps1 , ps2" := (BuildInst "CTestSubset" ps1 ps2 pd scr0 csr0 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'cseal' pd , ps1 , ps2" := (BuildInst "CSeal" ps1 ps2 pd scr0 csr0 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'cunseal' pd , ps1 , ps2" := (BuildInst "CUnseal" ps1 ps2 pd scr0 csr0 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.

Notation "'beq' ps1 , ps2 , pimm" := (BuildInst "BEq" ps1 ps2 x0 scr0 csr0 pimm%Z true) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'bne' ps1 , ps2 , pimm" := (BuildInst "BNE" ps1 ps2 x0 scr0 csr0 pimm%Z true) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'blt' ps1 , ps2 , pimm" := (BuildInst "BLT" ps1 ps2 x0 scr0 csr0 pimm%Z true) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'bge' ps1 , ps2 , pimm" := (BuildInst "BGE" ps1 ps2 x0 scr0 csr0 pimm%Z true) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'bltu' ps1 , ps2 , pimm" := (BuildInst "BLTU" ps1 ps2 x0 scr0 csr0 pimm%Z true) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'bgeu' ps1 , ps2 , pimm" := (BuildInst "BGEU" ps1 ps2 x0 scr0 csr0 pimm%Z true) (at level 65, only parsing): cheriot_assembly_scope.

Notation "'clb' pd , pimm #[ ps1 ]" := (BuildInst "CLB" ps1 x0 pd scr0 csr0 pimm%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'clh' pd , pimm #[ ps1 ]" := (BuildInst "CLh" ps1 x0 pd scr0 csr0 pimm%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'clw' pd , pimm #[ ps1 ]" := (BuildInst "CLW" ps1 x0 pd scr0 csr0 pimm%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'clbu' pd , pimm #[ ps1 ]" := (BuildInst "CLBU" ps1 x0 pd scr0 csr0 pimm%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'clhu' pd , pimm #[ ps1 ]" := (BuildInst "CLHU" ps1 x0 pd scr0 csr0 pimm%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'clc' pd , pimm #[ ps1 ]" := (BuildInst "CLC" ps1 x0 pd scr0 csr0 pimm%Z false) (at level 65, only parsing): cheriot_assembly_scope.

Notation "'csb' pimm #[ ps1 ], ps2" := (BuildInst "CSB" ps1 ps2 x0 scr0 csr0 pimm%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'csh' pimm #[ ps1 ], ps2" := (BuildInst "CSH" ps1 ps2 x0 scr0 csr0 pimm%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'csw' pimm #[ ps1 ], ps2" := (BuildInst "CSW" ps1 ps2 x0 scr0 csr0 pimm%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'csc' pimm #[ ps1 ], ps2" := (BuildInst "CSC" ps1 ps2 x0 scr0 csr0 pimm%Z false) (at level 65, only parsing): cheriot_assembly_scope.

Notation "'cjal' pd , pimm" := (BuildInst "CJAL" x0 x0 pd scr0 csr0 pimm%Z true) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'cj' pimm" := (BuildInst "CJAL" x0 x0 x0 scr0 csr0 pimm%Z true) (at level 65, only parsing): cheriot_assembly_scope.

Notation "'cjalr' pd , ps1" := (BuildInst "CJALR" ps1 x0 pd scr0 csr0 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'cjr' ps1" := (BuildInst "CJALR" ps1 x0 x0 scr0 csr0 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.

Notation "'ecall'" := (BuildInst "ECall" x0 x0 x0 scr0 csr0 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'mret'" := (BuildInst "MRet" x0 x0 x0 scr0 csr0 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'fence: cheriot_assembly_scope.i'" := (BuildInst "FenceI" x0 x0 x0 scr0 csr0 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.

Notation "'csrrw' pd , csrId , ps1" := (BuildInst "CSRRW" ps1 x0 pd scr0 csrId 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'csrrs' pd , csrId , ps1" := (BuildInst "CSRRS" ps1 x0 pd scr0 csrId 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'csrrc' pd , csrId , ps1" := (BuildInst "CSRRC" ps1 x0 pd scr0 csrId 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.

Notation "'csrw' csrId , ps1" := (BuildInst "CSRRW" ps1 x0 x0 scr0 csrId 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'csrs' csrId , ps1" := (BuildInst "CSRRS" ps1 x0 x0 scr0 csrId 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'csrc' csrId , ps1" := (BuildInst "CSRRC" ps1 x0 x0 scr0 csrId 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.

Notation "'csrr' pd , csrId" := (BuildInst "CSRRW" x0 x0 pd scr0 csrId 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.

Notation "'csrrwi' pd , csrId , pimm" := (BuildInst "CSRRWI" x0 x0 pd scr0 csrId pimm%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'csrrsi' pd , csrId , pimm" := (BuildInst "CSRRSI" x0 x0 pd scr0 csrId pimm%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'csrrci' pd , csrId , pimm" := (BuildInst "CSRRCI" x0 x0 pd scr0 csrId pimm%Z false) (at level 65, only parsing): cheriot_assembly_scope.

Notation "'csrwi' csrId , pimm" := (BuildInst "CSRRWI" x0 x0 x0 scr0 csrId pimm%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'csrsi' csrId , pimm" := (BuildInst "CSRRSI" x0 x0 x0 scr0 csrId pimm%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'csrci' csrId , pimm" := (BuildInst "CSRRCI" x0 x0 x0 scr0 csrId pimm%Z false) (at level 65, only parsing): cheriot_assembly_scope.

Notation "'cspecialrw' pd , scrId , ps1" := (BuildInst "CSpecialRW" ps1 x0 pd scrId csr0 0%Z false)
                                              (at level 65, only parsing): cheriot_assembly_scope.
Notation "'cspecialr' pd , scrId" := (BuildInst "CSpecialRW" x0 x0 pd scrId csr0 0%Z false) (at level 65, only parsing): cheriot_assembly_scope.
Notation "'cspecialw' scrId , ps1" := (BuildInst "CSpecialRW" ps1 x0 x0 scrId csr0 0%Z false)
                                        (at level 65, only parsing): cheriot_assembly_scope.

Local Close Scope cheriot_assembly_scope.
