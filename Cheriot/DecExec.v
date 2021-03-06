Require Import Kami.AllNotations ProcKami.Cheriot.Lib ProcKami.Cheriot.Types.

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

  Definition matchField (f: FieldRange) :=
    let '(existT (start, size) field) := f in
    UniBit (TruncMsb start size) (ZeroExtendTruncLsb (start + size) inst) ==
      Const ty field.

  Definition matchUniqId (uid: UniqId) :=
    CABool And (map matchField uid).

  Section ListInstEntry.
    Variable ik: Kind.
    Variable ls: list (InstEntry ik).

    Let finLs := finTagMap (fun x => (instName x, Bool)) ls.

    Definition MatchInstEntryStruct: Kind :=
      StructKind (fun x => instName x) (fun _ => Bool) ls.

    Definition matchInstEntry: MatchInstEntryStruct ## ty :=
      structLet (fun x => instName x) (fun _ => Bool)
        (fun x => RetE (matchUniqId (uniqId x))) ls.

    Section matches.
      Variable matches: MatchInstEntryStruct @# ty.
      Definition decodeInstEntry : Maybe ik ## ty :=
        redLet (@Kor _ (Maybe ik))
          (fun x => ( LETE out <- inputXform (snd x) pc inst cs1 cs2 scr csr;
                      RetE ((ITE (castReadStructExpr _ (ReadStruct matches (fst x)))
                               (Valid #out)
                               Invalid) : Maybe ik @# ty)))
          finLs.

      Section InstProperties.
        Variable k: Kind.
        Variable f: InstEntry ik -> k @# ty.
        Definition propertiesInstEntry: k @# ty :=
          Kor (map (fun x => ITE (castReadStructExpr _ (ReadStruct matches (fst x)))
                               (f (snd x))
                               (Const ty Default) )
                 finLs).
      End InstProperties.
    End matches.

    Section Exec.
      Variable func: ik @# ty -> FuncOutput ## ty.
      Definition execInstEntry (decodes: Maybe ik @# ty) : Maybe FuncOutput ## ty :=
        ( LETE ret <- func (decodes @% "data");
          RetE (STRUCT { "valid" ::= decodes @% "valid";
                         "data" ::= #ret } : Maybe FuncOutput @# ty)).
    End Exec.
  End ListInstEntry.

  Section FuncEntry.
    Variable ls: list FuncEntry.

    Let finLs := finTagMapPf (fun x => ((funcName x ++ "_match")%string, MatchInstEntryStruct (insts x))) ls.

    Definition MatchFuncEntryStruct: Kind :=
      StructKind (fun x => (funcName x ++ "_match")%string) (fun x => MatchInstEntryStruct (insts x)) ls.

    Definition matchFuncEntry: MatchFuncEntryStruct ## ty :=
      structLet _  _ (fun x => matchInstEntry (insts x)) ls.

    Definition DecodeFuncEntryStruct: Kind :=
      StructKind (fun x => funcName (finTagMapVal x)) (fun x => Maybe (localFuncInput (finTagMapVal x))) finLs.

    Section allMatches.
      Variable allMatches: MatchFuncEntryStruct @# ty.
      Definition decodeFuncEntry : DecodeFuncEntryStruct ## ty.
        refine
          (structLet _ _
             (fun x => ( LETC matches <- ReadStruct allMatches (finTagMapFin x);
                         decodeInstEntry (ls := insts (finTagMapVal x))
                           (_ #matches) )) finLs).
        rewrite (finTagMapPrf x).
        exact id.
      Defined.

      Section InstProperties.
        Variable k: Kind.
        Variable f: forall ik, InstEntry ik -> k @# ty.

        Definition propertiesFuncEntry: k @# ty.
          refine
            (Kor
               (map (fun x => propertiesInstEntry (_ (ReadStruct allMatches (finTagMapFin x)))
                                (@f _)) finLs)).
          rewrite (finTagMapPrf x).
          exact id.
        Defined.
      End InstProperties.

      Definition hasCs1PropFn := propertiesFuncEntry (fun _ x => Const ty (hasCs1 (instProperties x))).
      Definition hasCs2PropFn := propertiesFuncEntry (fun _ x => Const ty (hasCs2 (instProperties x))).
      Definition hasScrPropFn := propertiesFuncEntry (fun _ x => Const ty (hasScr (instProperties x))).
      Definition hasCsrPropFn := propertiesFuncEntry (fun _ x => Const ty (hasCsr (instProperties x))).
      Definition implicitReadPropFn := propertiesFuncEntry
                                         (fun _ x => Const ty (natToWord RegIdSz (implicit (instProperties x)))).
      Definition implicitMepccPropFn := propertiesFuncEntry (fun _ x => Const ty (implicitMepcc (instProperties x))).
      Definition implicitIePropFn := propertiesFuncEntry (fun _ x => Const ty (implicitIe (instProperties x))).
    End allMatches.

    Definition execFuncEntry (allDecodes: DecodeFuncEntryStruct @# ty): Maybe FuncOutput ## ty.
      refine
        (redLet (@Kor _ (Maybe FuncOutput))
           (fun x => ( LETC decodes <- ReadStruct allDecodes (finTagMapFin x);
                       execInstEntry (@localFunc _ (finTagMapVal (finTagMapVal x)) ty) (_ #decodes) ))
           (finTagMapPf
              (fun x => (funcName (finTagMapVal x), Maybe (localFuncInput (finTagMapVal x)))) finLs)).
      rewrite (finTagMapPrf x).
      exact id.
    Defined.
  End FuncEntry.
End DecExec.
