Require Import Kami.AllNotations Coq.Sorting.Mergesort Coq.Structures.Orders.

Notation "### x" := (Var type (SyntaxKind _) x) (no associativity, at level 0): kami_expr_scope.

Section TruncExtend.
  Variable ty: Kind -> Type.
  Definition ZeroExtendTo outSz inSz (e: Bit inSz @# ty) := ZeroExtend (outSz - inSz) e.
  Definition SignExtendTo outSz inSz (e: Bit inSz @# ty) := SignExtend (outSz - inSz) e.
  Definition TruncLsbTo outSz restSz (e: Bit (outSz + restSz) @# ty) := UniBit (TruncLsb outSz restSz) e.
  Definition TruncMsbTo outSz restSz (e: Bit (restSz + outSz) @# ty) := UniBit (TruncMsb restSz outSz) e.
End TruncExtend.

Fixpoint convTypeToConst [k: Kind] : forall (t: type k), ConstT k :=
  match k return type k -> ConstT k with
  | Bool => fun b => ConstBool b
  | Bit k => fun w => ConstBit w
  | Struct n fk => fun fv => ConstStruct fk (fun i => convTypeToConst (fv i))
  | Array n k => fun fv => ConstArray (fun i => convTypeToConst (fv i))
  end.

Definition convConstArrayToFunConst [n: nat] [k: Kind] (v: Fin.t n -> type k): Fin.t n -> (ConstT k) :=
  fun i => convTypeToConst (v i).

Section FinTag.
  Variable A: Type.
  Fixpoint finTag (ls: list A): list (Fin.t (length ls) * A) :=
    match ls return list (Fin.t (length ls) * A) with
    | nil => nil
    | x :: xs => (Fin.F1, x) :: map (fun y => (Fin.FS (fst y), snd y)) (finTag xs)
    end.

  Section FinTagMap.
    Variable B: Type.
    Variable f: A -> B.
    Fixpoint finTagMap (ls: list A): list (Fin.t (length (map f ls)) * A) :=
      match ls return list (Fin.t (length (map f ls)) * A) with
      | nil => nil
      | x :: xs => (Fin.F1, x) ::
                     map (fun y => (Fin.FS (fst y), snd y)) (finTagMap xs)
      end.

    Fixpoint finTagMapPf2 (ls: list A):
      list {x: (Fin.t (length (map f ls)) * A) & nth_Fin (map f ls) (fst x) = f (snd x)} :=
      match ls return list {x: (Fin.t (length (map f ls)) * A) & nth_Fin (map f ls) (fst x) = f (snd x)} with
      | nil => nil
      | x :: xs => existT _ (Fin.F1, x) eq_refl ::
                     map (fun y => existT (fun z =>
                                             nth_Fin (map f (x :: xs)) (fst z) =
                                               f (snd z)) (Fin.FS (fst (projT1 y)), snd (projT1 y))
                                     (projT2 y)) (finTagMapPf2 xs)
      end.

    Record FinTagMapPf ls :=
      { finTagMapFin: Fin.t (length (map f ls));
        finTagMapVal: A;
        finTagMapPrf: nth_Fin (map f ls) finTagMapFin = f finTagMapVal }.
    
    Fixpoint finTagMapPf (ls: list A): list (FinTagMapPf ls) :=
      match ls return list (FinTagMapPf ls) with
      | nil => nil
      | x :: xs => Build_FinTagMapPf (x :: xs) Fin.F1 eq_refl ::
                     map (fun y => Build_FinTagMapPf (x :: xs) (Fin.FS (finTagMapFin y)) (finTagMapPrf y))
                     (finTagMapPf xs)
      end.

  End FinTagMap.
End FinTag.

Section Reducer.
  Variable A: Type.
  Variable ty: Kind -> Type.

  Section Struct.
    Variable sMap: A -> string.

    Section SameKindStruct.
      Context {k: Kind}.
      Theorem structIndexSameKind ls i:
        (snd (nth_Fin (map (fun a => (sMap a, k)) ls) i)) = k.
      Proof.
        induction ls.
        - apply Fin.case0.
          exact i.
        - fin_dep_destruct i.
          + reflexivity.
          + apply IHls.
      Defined.

      Definition castReadStructExpr {ls i ty} (e: snd (nth_Fin (map (fun a => (sMap a, k)) ls) i) @# ty) : k @# ty :=
        eq_rect _ (fun x => x @# ty) e _ (structIndexSameKind ls i).
    End SameKindStruct.

    Variable kMap: A -> Kind.
    Definition StructKind ls := Struct (fun i => nth_Fin (map (fun x => (sMap x, kMap x)) ls) i).

    Section Let.
      Variable letMap: forall a, kMap a ## ty.

      Local Open Scope kami_expr.
      Local Fixpoint structLetHelp (exprs: list { x : string * Kind & snd x @# ty }) (ls: list A):
        Struct (fun i => nth_Fin (map (@projT1 _ _) exprs ++ map (fun x => (sMap x, kMap x)) ls) i) ## ty.
      refine
        (match ls with
         | nil => RetE (@eq_rect _ _ _ (getStructVal exprs) _ _)
         | x :: xs => ( LETE next : kMap x <- letMap x;
                        (@eq_rect _ _ _ (structLetHelp (exprs ++ [existT _ (sMap x, kMap x) #next]) xs) _ _) )
         end).
      - abstract (rewrite app_nil_r; reflexivity).
      - abstract (rewrite map_app, <- app_assoc; reflexivity).
      Defined.

      Definition structLet: forall ls, StructKind ls ## ty := structLetHelp [].
    End Let.

    Section Action.
      Variable actionMap: forall a, ActionT ty (kMap a).

      Local Open Scope kami_expr.
      Local Open Scope kami_action.
      Local Fixpoint structActionHelp (exprs: list { x : string * Kind & snd x @# ty }) (ls: list A):
        ActionT ty (Struct (fun i => nth_Fin (map (@projT1 _ _) exprs ++ map (fun x => (sMap x, kMap x)) ls) i)).
      refine
        (match ls with
         | nil => Ret (@eq_rect _ _ _ (getStructVal exprs) _ _)
         | x :: xs => ( LETA next : kMap x <- actionMap x;
                        (@eq_rect _ _ _ (structActionHelp (exprs ++ [existT _ (sMap x, kMap x) #next]) xs) _ _) )
         end).
      - abstract (rewrite app_nil_r; reflexivity).
      - abstract (rewrite map_app, <- app_assoc; reflexivity).
      Defined.

      Definition structAction: forall ls, ActionT ty (StructKind ls) := structActionHelp [].
    End Action.
  End Struct.

  Section Red.
    Variable K: Kind.
    Variable RK: Kind.
    Variable red: list (K @# ty) -> RK @# ty.
    
    Section Let.
      Variable letMap: A -> K ## ty.

      Local Open Scope kami_expr.
      Local Fixpoint redLetHelp (exprs: list (K @# ty)) (ls: list A): RK ## ty :=
        (match ls with
         | nil => RetE (red exprs)
         | x :: xs => ( LETE next : K <- letMap x;
                        redLetHelp (exprs ++ [#next]) xs )
         end).

      Definition redLet: forall ls, RK ## ty := redLetHelp [].
    End Let.

    Section Action.
      Variable actionMap: A -> ActionT ty K.

      Local Open Scope kami_expr.
      Local Open Scope kami_action.
      Local Fixpoint redActionHelp (exprs: list (K @# ty)) (ls: list A): ActionT ty RK :=
        (match ls with
         | nil => Ret (red exprs)
         | x :: xs => ( LETA next : K <- actionMap x;
                        redActionHelp (exprs ++ [#next]) xs )
         end).

      Definition redAction: forall ls, ActionT ty RK := redActionHelp [].
    End Action.
  End Red.
End Reducer.

Notation "'WriteIf' pred 'Then' reg : kind <- expr ; cont " :=
  ( ReadReg reg (SyntaxKind kind)
      (fun oldVal =>
         ( @WriteReg _ _ reg (SyntaxKind kind) (ITE pred expr (Var _ (SyntaxKind kind) oldVal))
             cont)))%kami_action
    (at level 13, right associativity, reg at level 99) : kami_action_scope.

Record RegInfo n := {
    regAddr : word n;
    regName : string }.

Definition getAddrFromInfo (name: string) n (regs: list (RegInfo n)) :=
  match find (fun x => String.eqb name (regName x)) regs with
  | Some x => regAddr x
  | None => wzero _
  end.

Local Open Scope kami_action.
Definition readRegs prefix n (regs: list (RegInfo n)) ty (addr: Bit n @# ty) k : ActionT ty k :=
  redAction (@Kor _ k)
    (fun x => ( If (addr == Const ty (regAddr x))
                then ( Read retVal : k <- ((prefix ++ "_") ++ (regName x))%string;
                       Ret #retVal )
                else Ret (Const ty Default) as ret;
                Ret #ret )) regs.

Definition writeRegsPred prefix n (regs: list (RegInfo n)) ty
  (pred: Bool @# ty) (addr: Bit n @# ty) k (val: k @# ty) :=
  fold_right (fun x rest => ( If (addr == Const ty (regAddr x))
                              then (WriteIf pred Then ((prefix ++ "_") ++ (regName x))%string : k <- val; Retv)
                              else Retv;
                              rest ) ) Retv regs.

Definition writeRegs prefix n (regs: list (RegInfo n)) ty (addr: Bit n @# ty) k (val: k @# ty) :=
  fold_right (fun x rest => ( If (addr == Const ty (regAddr x))
                              then ( Write ((prefix ++ "_") ++ (regName x))%string : k <- val; Retv )
                              else Retv;
                              rest ) ) Retv regs.

Definition callReadRegFile k (name: string) ty n (idx: Bit n @# ty) : ActionT ty k :=
  ( Call ret : Array 1 k <- name (idx: Bit n);
    Ret (ReadArrayConst #ret Fin.F1) ).

Definition callWriteRegFile (name: string) ty n (idx: Bit n @# ty) k (v: k @# ty) : ActionT ty Void :=
  ( Call name (STRUCT { "addr" ::= idx;
                        "data" ::= BuildArray (fun _ => v) } : WriteRq n (Array 1 k));
    Retv ).

Module Type ToNat.
  Parameter t: Type.
  Parameter toNat: t -> nat.
End ToNat.

Module NatOrder (toNat: ToNat) <: TotalLeBool.
  Definition t := toNat.t.
  Definition leb (x y: t) := Nat.leb (toNat.toNat x) (toNat.toNat y).
  Theorem leb_total : forall a1 a2, leb a1 a2 = true \/ leb a2 a1 = true.
  Proof.
    unfold leb; intros.
    rewrite ?Nat.leb_le.
    lia.
  Qed.
End NatOrder.

Module Interval <: ToNat.
  Definition t := (nat * nat)%type.
  Definition toNat (x: t) := fst x.
End Interval.

Module IntervalOrder := NatOrder Interval.
Module IntervalSort := Sort IntervalOrder.

Section IntervalList.
  Variable intervals: list (nat * nat).
  Let sorted := IntervalSort.sort intervals.

  Fixpoint getLastDisjointContiguous (start: nat) ls : option nat:=
    match ls with
    | nil => Some start
    | (s, l) :: xs => if (s =? start) && negb (l =? 0)
                      then getLastDisjointContiguous (s + l) xs
                      else None
    end.

  Definition getDisjointContiguous : option (nat * nat) :=
    match sorted with
    | nil => Some (0, 0)
    | (s, l) :: xs => match getLastDisjointContiguous s sorted with
                      | Some final => Some (s, final)
                      | None => None
                      end
    end.
End IntervalList.

Module SigWord <: ToNat.
  Definition t := {x : (nat * nat) & word (snd x) }.
  Definition toNat (x: t) := fst (projT1 x).
End SigWord.

Module SigWordOrder := NatOrder SigWord.
Module SigWordSort := Sort SigWordOrder.

Module SigTriple <: ToNat.
  Definition t := (nat * (nat * nat))%type.
  Definition toNat (x: t) := fst x.
End SigTriple.

Module SigTripleOrder := NatOrder SigTriple.
Module SigTripleSort := Sort SigTripleOrder.

Section WordCombiner.
  Variable initPos initSz: nat.
  Variable init: word initSz.
  Fixpoint wordCombiner (ls: list {x: nat * nat & word (snd x)}) :=
    match ls return word (fold_right (fun new sum => sum + snd (projT1 new)) initSz ls) with
    | nil => init
    | x :: xs => wcombine (wordCombiner xs) (projT2 x)
    end.
End WordCombiner.

Section BitsCombiner.
  Variable ty: Kind -> Type.
  Variable initPos initSz: nat.
  Variable init: Bit initSz @# ty.

  Fixpoint bitsCombiner (ls: list {x: nat * nat & Bit (snd x) @# ty}) :=
    match ls return Bit (fold_right (fun new sum => snd (projT1 new) + sum) initSz ls) @# ty with
    | nil => init
    | x :: xs => BinBit (Concat _ _) (bitsCombiner xs) (projT2 x)
    end.
End BitsCombiner.

Definition extractWord n (w: word n) (start width: nat): word width :=
  @truncMsb width (start + width) (@truncLsb (start + width) _ w).

Section InsertListIntoFinMap.
  Variable A: Type.
  Variable sz: nat.
  Variable arr: Fin.t sz -> A.
  Variable ls: list A.
  Variable start: nat.
  
  Definition insertListIntoFinMap (iFin: Fin.t sz) :=
    let i := FinFun.Fin2Restrict.f2n iFin in
    if (start <=? i) && (i <? start + (length ls))
    then nth (i - start) ls (arr iFin)
    else arr iFin.
End InsertListIntoFinMap.

Section RmStringPrefix.
  Fixpoint rmStringPrefix n (s: string) :=
    match n with
    | 0 => s
    | S m => match s with
             | String c s' => rmStringPrefix m s'
             | EmptyString => EmptyString
             end
    end.

  Theorem rmAppend (p s: string): rmStringPrefix (String.length p) (p ++ s)%string = s.
  Proof.
    induction p; auto.
  Qed.
End RmStringPrefix.

Theorem string_dec_eqb s1 s2: String.eqb s1 s2 = getBool (string_dec s1 s2).
Proof.
  destruct (string_dec s1 s2).
  - rewrite eqb_eq; auto.
  - rewrite eqb_neq; auto.
Qed.

Section EvalProp.
  Variable A: Type.
  Variable R: A -> A -> bool.

  Fixpoint NoDupEval (ls: list A) :=
    match ls with
    | nil => true
    | x :: xs => andb (negb (existsb (R x) xs)) (NoDupEval xs)
    end.

  Section NoDupEvalCorrect.
    Variable RIsDec: forall a1 a2, R a1 a2 = true <-> a1 = a2.

    Lemma NoDupEvalCorrect1 ls: NoDupEval ls = true -> NoDup ls.
    Proof.
      induction ls; intros; constructor;
        simpl in H;
        rewrite andb_true_iff in H;
        destruct H.
      - intro.
        rewrite <- eq_true_not_negb_iff in H.
        rewrite existsb_exists in H.
        assert (rhs: exists x, In x ls /\ (R a) x = true).
        { exists a.
          constructor; auto.
          rewrite (RIsDec a a); auto.
        }
        apply H; auto.
      - apply IHls; auto.
    Qed.

    Lemma NoDupEvalCorrect2 ls: NoDup ls -> NoDupEval ls = true.
    Proof.
      induction 1; auto.
      simpl.
      rewrite andb_true_iff.
      constructor; [|auto].
      rewrite <- eq_true_not_negb_iff.
      rewrite existsb_exists.
      intro.
      destruct H1 as [ x0 [in1 r1]].
      rewrite RIsDec in r1; subst.
      apply H; auto.
    Qed.

    Theorem NoDupEvalCorrect ls: NoDup ls <-> NoDupEval ls = true.
    Proof.
      constructor.
      - apply NoDupEvalCorrect2.
      - apply NoDupEvalCorrect1.
    Qed.
  End NoDupEvalCorrect.
  
  Fixpoint ForallOrdPairsEval (ls: list A) :=
    match ls with
    | nil => true
    | x :: xs => andb (forallb (R x) xs) (ForallOrdPairsEval xs)
    end.
End EvalProp.
  
