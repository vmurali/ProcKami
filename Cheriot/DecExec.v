Require Import Kami.AllNotations ProcKami.Cheriot.Types.

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
