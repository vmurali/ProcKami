Require Import Kami.AllNotations.

Record Instruction := {
    instAsmName : string;
    cs1         : Z;
    cs2         : Z;
    cd          : Z;
    csr         : Z;
    immVal      : Z }.

Inductive AssemblyError := InstAsmName | Cs1 | Cs2 | Cd | Csr | Imm.

Definition getInstructionRel (inst: Instruction) (curr: Z) (immRel: bool) :=
  match immRel with
  | false => inst
  | true => let '(Build_Instruction name cs1Idx cs2Idx cdIdx csrIdx immV) := inst in
            Build_Instruction name cs1Idx cs2Idx cdIdx csrIdx (immV - curr)%Z
  end.

Inductive Prog :=
| ProgInst (inst: Instruction) (immRel: bool)
| ProgSeq (p1 p2: Prog)
| ProgDeclLabel (cont: Z -> Prog)
| ProgLabel (label: Z)
| ProgData (size: Z) (val: list (word 8))
| ProgAlign (size: Z).

Declare Scope assembly_scope.
Delimit Scope assembly_scope with assembly.
Infix ";;" := ProgSeq (at level 62, right associativity): assembly_scope.
Notation "'LOCAL' l ';' p" := (ProgDeclLabel (fun l => p)) (at level 65, l ident, right associativity): assembly_scope.
Notation "l ':;'" := (ProgLabel l) (at level 8, no associativity, format "l ':;'"): assembly_scope.
Notation "l ':;;' p" := (ProgSeq (ProgLabel l) p) (at level 8, p at level 65, right associativity, format "l ':;;' p"): assembly_scope.
Notation "'.align' sz" := (ProgAlign sz%Z) (at level 65): assembly_scope.
Notation "'.byte' val" := (ProgData 1%Z [ZToWord 8 val]) (at level 65): assembly_scope.
Notation "'.hword' val" := (ProgData 2%Z [ZToWord 8 val; ZToWord 8 (val/(Z.pow 2 8))]) (at level 65): assembly_scope.
Notation "'.word' val" := (ProgData 4%Z [ZToWord 8 val; ZToWord 8 (val/(Z.pow 2 8)); ZToWord 8 (val/(Z.pow 2 16)); ZToWord 8 (val/(Z.pow 2 24))]) (at level 65): assembly_scope.
Notation "'.dword' val" :=
  (ProgData 4%Z [ZToWord 8 val; ZToWord 8 (val/(Z.pow 2 8)); ZToWord 8 (val/(Z.pow 2 16)); ZToWord 8 (val/(Z.pow 2 24));
                 ZToWord 8 (val/(Z.pow 2 32)); ZToWord 8 (val/(Z.pow 2 40)); ZToWord 8 (val/(Z.pow 2 48)); ZToWord 8 (val/(Z.pow 2 56))]) (at level 65): assembly_scope.

Inductive ResolvedProg :=
| ResolvedProgInst (inst: Instruction) (immRel: bool)
| ResolvedProgSeq (p1 p2: ResolvedProg)
| ResolvedProgData (size: Z) (val: list (word 8))
| ResolvedProgAlign (size: Z).

Section Assembler.
  Variable instEncoder: Instruction -> (list (word 8) + AssemblyError)%type.
  Variable startAlign: Z.

  Definition instSize (inst: Instruction) := match instEncoder inst with
                                             | inl xs => Z.of_nat (length xs)
                                             | inr _ => 0%Z
                                             end.

  Definition getNextAlignDiff (sz curr: Z) :=
    let realCurr := Z.modulo (Z.pow 2 startAlign + curr) sz in
    (Z.modulo (sz - realCurr) sz)%Z.
  
  Fixpoint getAddrMap (prog: Prog) (currLabelAddrMap: Z * Z * (Z -> Z)): Z * Z * (Z -> Z) :=
    match prog with
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

  Fixpoint countTrailingZerosPositive (x: positive) :=
    match x with
    | (p~0)%positive => Z.succ (countTrailingZerosPositive p)
    | _ => 0%Z
    end.

  Definition countTrailingZerosZ (x: Z) :=
    match x with
    | Zpos p => countTrailingZerosPositive p
    | _ => 0%Z
    end.

  Fixpoint getInstBytesResolved (prog: ResolvedProg) (curr: Z) (idx: nat): (((list (word 8) * Z) + (AssemblyError * Prog))%type * nat) :=
    match prog with
    | ResolvedProgInst inst immRel =>
        let mInstBytes :=
          ltac:(let y := eval simpl in (instEncoder (getInstructionRel inst curr immRel)) in exact y) in
        match mInstBytes with
        | inl instBytes => (inl (instBytes, curr + Z.of_nat (length instBytes))%Z, S idx)
        | inr err => (inr (err, ProgInst inst immRel), idx)
        end
    | ResolvedProgSeq p1 p2 => match getInstBytesResolved p1 curr idx with
                               | (inl (p1', c2), i2) => match getInstBytesResolved p2 c2 i2 with
                                                        | (inl (p2', c), i) => (inl (p1' ++ p2', c), i)
                                                        | (inr errProg, i) => (inr errProg, i)
                                                        end
                               | (inr errProg, i) => (inr errProg, i)
                               end
    | ResolvedProgData size vals => (inl (firstn (Z.to_nat size) vals, curr + size)%Z, S idx)
    | ResolvedProgAlign size =>
        let len := getNextAlignDiff size curr in
        (inl (repeat (wzero 8) (Z.to_nat len), curr + len)%Z, S idx)
    end.

  (* Bytes of instruction or the first error with assembly instruction and a line number *)
  Definition getInstBytes (prog: Prog): ((list (word 8)) + (AssemblyError * Prog * nat))%type :=
    let '(_, _, addrMap) := getAddrMap prog (0%Z, 0%Z, fun i => (-1)%Z) in
    let '(resolved, _) := setLabel addrMap prog 0%Z in
    match getInstBytesResolved resolved 0%Z 0 with
    | (inl (xs, _), _) => inl xs
    | (inr errProg, line) => inr (errProg, line)
    end.
End Assembler.
