Require Import Kami.AllNotations ProcKami.Cheriot.Types.

Section Reducer.
  Variable A: Type.
  Variable ty: Kind -> Type.

  Section Struct.
    Variable kMap: A -> Kind.
    Variable sMap: A -> string.

    Section SameKindStruct.
      Theorem lsSameKind (k: Kind) ls: forall i,
          snd (nth i (map (fun a => (sMap a, k)) ls) ("", k)) = k.
      Proof.
        induction ls; simpl; destruct i; auto.
      Qed.
      
      Theorem structSameKind (k: Kind) ls i:
        (snd (nth_Fin (map (fun a => (sMap a, k)) ls) i)) = k.
      Proof.
        rewrite (@nth_Fin_nth _ ("", k) _).
        rewrite lsSameKind; auto.
      Qed.
    End SameKindStruct.

    Definition RedStructKind ls := Struct (fun i => nth_Fin (map (fun x => (sMap x, kMap x)) ls) i).

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

      Definition structLet: forall ls, RedStructKind ls ## ty := structLetHelp [].
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

      Definition structAction: forall ls, ActionT ty (RedStructKind ls) := structActionHelp [].
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
    Variable name: string.

    Definition MatchStruct: list ((nat * InstEntry k)) -> Kind :=
      RedStructKind (fun _ => Bool) (fun x => instName (snd x))%string.

    Definition matchListInstEntry: forall ls, MatchStruct ls ## ty :=
      structLet (fun _ => Bool) (fun x => instName (snd x))%string
        (fun x => RetE (matchUniqId (uniqId (snd x)))).

    Definition decodeListInstEntry ls: MatchStruct ls @# ty -> Maybe k ## ty.
      refine
        (match ls return MatchStruct ls @# ty -> Maybe k ## ty with
         | nil => fun _ => RetE Invalid
         | e :: es =>
             fun matches =>
               redLet (@Kor _ (Maybe k))
                 (fun x =>
                    ( LETE out <- inputXform (snd x) pc inst cs1 cs2 scr csr ie;
                      RetE
                        ((ITE (eq_rect _ _ (ReadStruct matches ( natToFin (fst x) _ )) _ _)
                            (Valid #out)
                            Invalid): Maybe k @# ty)) )
                 (e :: es)
         end).
      abstract (rewrite structSameKind; auto).
    Defined.
  End ListInstEntry.

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

  Section FuncEntry.
    (*
    Variable fs: list FuncEntry.

    Definition DecOut := Struct (fun i => localFuncInput (nth_Fin fs i))
                           (fun i => funcName (nth_Fin fs i)).
     *)

  End FuncEntry.
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
End DecExec.
