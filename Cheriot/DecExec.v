Require Import Kami.AllNotations ProcKami.Cheriot.Types ProcKami.Cheriot.Lib.

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
          (fun x => ( LETE out <- inputXform (snd x) pc inst cs1 cs2 scr csr ie;
                      RetE ((ITE (castReadStructExpr _ (ReadStruct matches (fst x)))
                               (Valid #out)
                               Invalid) : Maybe ik @# ty)))
          finLs.

      Section InstProperties.
        Variable f: InstProperties -> bool.
        Definition propertiesInstEntry: Bool @# ty :=
          Kor (map (fun x => Const ty (f (instProperties (snd x))) &&
                               castReadStructExpr _ (ReadStruct matches (fst x)))
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
        Variable f: InstProperties -> bool.

        Definition propertiesFuncEntry: Bool @# ty.
          refine
            ((@Kor _ Bool)
               (map (fun x => propertiesInstEntry (_ (ReadStruct allMatches (finTagMapFin x))) f) finLs)).
          rewrite (finTagMapPrf x).
          exact id.
        Defined.
      End InstProperties.

      Definition hasCs1Prop := propertiesFuncEntry hasCs1.
      Definition hasCs2Prop := propertiesFuncEntry hasCs2.
      Definition hasScrProp := propertiesFuncEntry hasScr.
      Definition hasCsrProp := propertiesFuncEntry hasCsr.
      Definition implicit3Prop := propertiesFuncEntry (fun p => Nat.eqb (implicit p) 3).
      Definition implicitMepccProp := propertiesFuncEntry implicitMepcc.
      Definition implicitIeProp := propertiesFuncEntry implicitIe.

    (* TODOs :
     - Write the efficient versions of "get" and "real" which calls propertiesFuncEntry only once
     *)

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
