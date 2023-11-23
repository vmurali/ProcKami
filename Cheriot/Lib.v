Require Import Kami.AllNotations.

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

Section RegAccess.  
  (* TODO: Index this with Kind of the register *)
  Record RegInfo n := {
      regAddress : word n;
      regInit : RegInitT }.

  Definition getAddrFromInfo (name: string) n (regs: list (RegInfo n)) :=
    match find (fun x => String.eqb (fst (regInit x)) name) regs with
    | Some x => regAddress x
    | None => wzero _
    end.

  Local Open Scope kami_action.
  Definition readRegs prefix n (regs: list (RegInfo n)) k ty (e: Bit n @# ty) :=
    redAction (@Kor _ k)
      (fun x => ( match projT1 (snd (regInit x)) with
                  | SyntaxKind k' =>
                      if Kind_decb k k'
                      then (If (e == Const ty (regAddress x))
                            then ( Read retVal : k <- (prefix ++ "_" ++ (fst (regInit x)))%string;
                                   Ret #retVal )
                            else Ret (Const ty Default) as ret;
                            Ret #ret )
                      else Ret (Const ty Default)
                  | _ => Ret (Const ty Default)
                  end)) regs.

  Definition callReadRegFile k (name: string) ty n (idx: Bit n @# ty) : ActionT ty k :=
    ( Call ret : Array 1 k <- name (idx: Bit n);
      Ret (ReadArrayConst #ret Fin.F1) ).
    
  Definition callWriteRegFile (name: string) ty n (idx: Bit n @# ty) k (v: k @# ty) : ActionT ty Void :=
    ( Call name (STRUCT { "addr" ::= idx;
                          "data" ::= BuildArray (fun _ => v) } : WriteRq n (Array 1 k));
      Retv ).
End RegAccess.

