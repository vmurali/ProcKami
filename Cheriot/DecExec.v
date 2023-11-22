Require Import Kami.AllNotations ProcKami.Cheriot.Types.

Axiom cheat: forall t, t.
    
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

Section FinTag.
  Variable A: Type.
  Fixpoint finTag (ls: list A): list (Fin.t (length ls) * A) :=
    match ls return list (Fin.t (length ls) * A) with
    | nil => nil
    | x :: xs => (Fin.F1, x) :: map (fun y => (Fin.FS (fst y), snd y)) (finTag xs)
    end.
  Variable B: Type.
  Variable f: A -> B.
  Fixpoint finTagMap (ls: list A): list (Fin.t (length (map f ls)) * A) :=
    match ls return list (Fin.t (length (map f ls)) * A) with
    | nil => nil
    | x :: xs => (Fin.F1, x) ::
                   map (fun y => (Fin.FS (fst y), snd y)) (finTagMap xs)
    end.
End FinTag.

Section DecExec.
  Context `{procParams: ProcParams}.
  Variable ty: Kind -> Type.
  Local Open Scope kami_expr.

  Variable pc: FullCap @# ty.
  Variable inst: Inst @# ty.
  Variable cs1: FullCapWithTag @# ty.
  Variable cs2: FullCapWithTag @# ty.
  Variable scr: FullCapWithTag @# ty.
  Variable csr: Data @# ty.
  Variable ie: Bool @# ty.

  Definition matchField (f: FieldRange) :=
    let '(existT (start, size) field) := f in
    UniBit (TruncMsb start size) (ZeroExtendTruncLsb (start + size) inst) ==
      Const ty field.

  Definition matchUniqId (uid: UniqId) :=
    CABool And (map matchField uid).

  Section ListInstEntry.
    Variable k: Kind.
    Variable ls: list (InstEntry k).

    Let finLs := finTagMap (fun x => (instName x, Bool)) ls.

    Definition MatchInstEntryStruct: Kind :=
      StructKind (fun x => instName x) (fun _ => Bool) ls.

    Definition matchInstEntry: MatchInstEntryStruct ## ty :=
      structLet (fun x => instName x) (fun _ => Bool)
        (fun x => RetE (matchUniqId (uniqId x))) ls.

    Definition decodeInstEntry (matches: MatchInstEntryStruct @# ty) : Maybe k ## ty :=
      redLet (@Kor _ (Maybe k))
        (fun x => ( LETE out <- inputXform (snd x) pc inst cs1 cs2 scr csr ie;
                    RetE ((ITE (castReadStructExpr _ (ReadStruct matches (fst x)))
                             (Valid #out)
                             Invalid) : Maybe k @# ty)))
        finLs.

    Section InstProperties.
      Variable f: InstProperties -> bool.
      Definition propertiesInstEntry (matches: MatchInstEntryStruct @# ty): Bool @# ty :=
        Kor (map (fun x => Const ty (f (instProperties (snd x))) &&
                             castReadStructExpr _ (ReadStruct matches (fst x)))
                 finLs).
    End InstProperties.
  End ListInstEntry.

  Section FuncEntry.
    Variable ls: list FuncEntry.
    Let fins := getFins (length ls).
    Let ifin := nth_Fin ls.
    Definition MatchFuncEntryStruct: Kind :=
      StructKind (fun i => (funcName (ifin i) ++ "_match")%string)
        (fun i => MatchInstEntryStruct (insts (ifin i))) fins.

    Definition matchFuncEntry: MatchFuncEntryStruct ## ty :=
      structLet _  _ (fun i => matchInstEntry (insts (ifin i))) fins.

    Definition decodeFuncEntry (allMatches : MatchFuncEntryStruct @# ty) :
      StructKind (fun i => funcName (ifin i)) (fun i => Maybe (localFuncInput (ifin i))) fins ## ty.
      refine
        (structLet (fun i => funcName (ifin i)) (fun i => Maybe (localFuncInput (ifin i)))
           (fun i => ( LETC matches <- ReadStruct allMatches (Fin.cast i _);
                       decodeInstEntry (ls := insts (ifin i)) (_ #matches) )) fins).
      Unshelve.
      2: abstract (rewrite map_length_red, getFins_length; reflexivity).
      abstract (rewrite nth_Fin_map_equiv_deduce, nth_Fin_getFins,
                 Fin_cast_cast_diff_deduce, Fin_cast_cast_same; exact id).
    Defined.

    Section InstProperties.
      Variable name: string.
      Variable f: InstProperties -> bool.
      Definition PropertiesFuncEntryStruct: Kind :=
        StructKind (fun i => (funcName (ifin i) ++ "_" ++ name))%string (fun _ => Bool) fins.

      Definition propertiesFuncEntry (allMatches: MatchFuncEntryStruct @# ty): PropertiesFuncEntryStruct ## ty.
        refine
          (structLet (fun i => (funcName (ifin i) ++ "_" ++ name)%string) (fun _ => Bool)
             (fun i => RetE (propertiesInstEntry f (_ (ReadStruct allMatches (Fin.cast i _))))) fins).
        Unshelve.
        2: abstract (rewrite map_length_red, getFins_length; reflexivity).
        3: exact (insts (ifin i)).
        - abstract (rewrite nth_Fin_map_equiv_deduce, nth_Fin_getFins,
                     Fin_cast_cast_diff_deduce, Fin_cast_cast_same; exact id).
      Defined.
    End InstProperties.
  End FuncEntry.

  Section ListFuncEntry.
    Variable k: Kind.

    Section Decode.
      Variable decOutput: Kind.
      Local Fixpoint decodeHelp (ls: list (InstEntry decOutput)) (exprs: list (decOutput @# ty)) : decOutput ## ty :=
        match ls with
        | nil => RetE (Kor exprs)
        | i :: rest => ( LETE decI <- inputXform i pc inst cs1 cs2 scr csr ie;
                         LETC matchI <- matchUniqId (uniqId i);
                         decodeHelp rest (ITE #matchI #decI (Const ty Default) :: exprs) )
        end.

      Section InstProperties.
        Variable f: InstProperties -> bool.
        
        Local Fixpoint getInstPropertiesHelp (ls: list (InstEntry decOutput)) (exprs: list (Bool @# ty)): Bool ## ty :=
          match ls with
          | nil => RetE (Kor exprs)
          | i :: rest => ( LETC matchI <- matchUniqId (uniqId i);
                           getInstPropertiesHelp rest (!#matchI || $$(f (instProperties i)) :: exprs) )
          end.

        Definition getInstProperties (ls: list (InstEntry decOutput)) := getInstPropertiesHelp ls [].
      End InstProperties.

      Definition decode (ls: list (InstEntry decOutput)) := decodeHelp ls [].
      
      Definition decodeMatch (ls: list (InstEntry decOutput)) :=
        Kor (map (fun i => matchUniqId (uniqId i)) ls).
    End Decode.

    Definition funcEntryExec (funcEntry: FuncEntry) (decOut: localFuncInput funcEntry ## ty) : FuncOutput ## ty :=
      ( LETE decOutput <- decOut;
        LETC decMatch <- decodeMatch (insts funcEntry);
        LETE fuOut <- localFunc funcEntry #decOutput;
        LETE execOut <- outputXform funcEntry #fuOut;
        RetE (ITE #decMatch #execOut (Const ty Default)) ).

    Definition fullDec (ls: list FuncEntry) := map (fun f => existT _ f (decode (insts f))) ls.

    Local Fixpoint fullExecHelp (ls: list {f: FuncEntry & localFuncInput f ## ty } )
      (exprs: list (FuncOutput @# ty)) : FuncOutput ## ty :=
      match ls with
      | nil => RetE (Kor exprs)
      | existT f decOut :: rest => ( LETE execOut <- funcEntryExec f decOut;
                                     fullExecHelp rest (#execOut :: exprs) )
      end.

    Definition fullExec (ls: list {f: FuncEntry & localFuncInput f ## ty }) := fullExecHelp ls [].

    Definition fullDecExec (ls: list FuncEntry) := fullExec (fullDec ls).
  End ListFuncEntry.
End DecExec.
