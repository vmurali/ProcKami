Require Import Kami.AllNotations ProcKami.Cheriot.Lib ProcKami.Cheriot.Types ProcKami.Cheriot.InstSpec.

Ltac getOrIntrosLtacHelp val ls :=
  match ls with
  | (val, _) :: _ => uconstr:(or_introl eq_refl)
  | (?x, _) :: ?xs => let y := getOrIntrosLtacHelp val xs in uconstr:(or_intror y)
  end.

Ltac dischargeWfActionT :=
  cbv [regName scrRegInfo csrRegInfo filter];
  match goal with
  | |- @WfActionT _ _ _ (convertLetExprSyntax_ActionT ?e) => apply WfLetExprSyntax_regs
  | |- @WfActionT _ _ _ _ => econstructor; eauto
  | |- In (?val, _) (getKindAttr ?ls) =>
      let y := (getOrIntrosLtacHelp val ls) in exact y
  | |- forall _, _ => intros
  | |- _ -> _ => intros 
  end.

Ltac getOrIntrosLtac :=
  match goal with
  | |- In (?val, _) (getKindAttr ?ls) =>
      let y := (getOrIntrosLtacHelp val ls) in exact y
  end.

Ltac repeatConj :=
  repeat match goal with
    | |- ?A /\ ?B => apply conj
    | |- _ => idtac
    end.

Ltac simpleNoDup :=
  match goal with
  | |- NoDup _ => apply (NoDupEvalCorrect1 String.eqb String.eqb_eq); auto
  end.

Ltac commonPrefixNoDup :=
  apply (NoDup_map_inv (rmStringPrefix (String.length (procName ++ "_"))%string)); cbv [map];
  rewrite ?rmAppend; simpleNoDup.

