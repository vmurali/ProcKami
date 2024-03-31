Require Import Kami.AllNotations.
Require Import ProcKami.Cheriot.Lib ProcKami.Cheriot.Types ProcKami.Cheriot.InstSpec ProcKami.Cheriot.RunSpec.

Section Prefix.
  Context `{coreConfigParams: CoreConfigParams}.
  Instance memParamsInst: MemParams := memParams.

  Local Notation "@^ x" := ((procName ++ "_") ++ x)%string (at level 0).
  Local Open Scope kami_expr.

  Definition specRules : list RuleT :=
    (@^"specTimerIncAndInterruptSetRule", specTimerIncAndInterruptSetRule) ::
      (@^"specTimerInterruptTakeRule", specTimerInterruptTakeRule scrList csrList) ::
      (@^"specInstBoundsExpcetionRule", specInstBoundsExceptionRule scrList csrList) ::
      (@^"specInstIllegalExceptionRule", fun ty => specInstIllegalExceptionRule scrList csrList ty specInstEntries) ::
      map (fun ie => (@^(append "specDecExecRule_" (instName ie)), fun ty => specDecExecRule scrList csrList ty ie))
      specInstEntries.

  Definition specRegs : list RegInitT :=
    (@^pcCapReg, existT _ (SyntaxKind Cap) (Some (SyntaxConst (convTypeToConst pcCapInit)))) ::
      (@^pcValReg, existT _ (SyntaxKind Addr) (Some (SyntaxConst (wcombine pcValInit (wzero 2))))) ::
      (@^regsArray, existT _ _ (Some (SyntaxConst (@convTypeToConst (Array 32 FullCapWithTag) regsInit)))) ::
      (@^memArray, existT _ _ (Some (SyntaxConst (@convTypeToConst (Array (NumMemBytes * NumBanks) (Bit 8))
                                                    memInit)))) ::
      (@^tagArray, existT _ _ (Some (SyntaxConst (ConstArray (fun (i: Fin.t NumMemBytes) => false))))) ::
      if hasTrap
      then
        (@^mtccReg,
          existT _ _ (Some (SyntaxConst
                              (convTypeToConst
                                 (evalExpr (STRUCT { "tag" ::= Const type true;
                                                     "cap" ::= ExecRootCapExpr type;
                                                     "val" ::= Const _ (wcombine mtccValInit (wzero 2))})))))) ::
          (@^mtdcReg,
            existT _ _ (Some (SyntaxConst
                                (convTypeToConst
                                   (evalExpr (STRUCT { "tag" ::= Const type true;
                                                       "cap" ::= DataRootCapExpr type;
                                                       "val" ::= Const _ (wcombine mtdcValInit (wzero 2))})))))) ::
          (@^mScratchCReg,
            existT _ _ (Some (SyntaxConst
                                (convTypeToConst
                                   (evalExpr (STRUCT { "tag" ::= Const type true;
                                                       "cap" ::= SealRootCapExpr type;
                                                       "val" ::= Const _ (wzero Xlen)})))))) ::
          (@^mepccReg, existT _ _ (Some (SyntaxConst (getDefaultConst FullCapWithTag)))) ::
          (@^mStatusReg, existT _ (SyntaxKind Data) (Some (SyntaxConst (wzero Xlen)))) ::
          (@^mieReg, existT _ (SyntaxKind Data) (Some (SyntaxConst (wzero Xlen)))) ::
          (@^mCauseReg, existT _ (SyntaxKind Data) None) ::
          (@^mtValReg, existT _ (SyntaxKind Data) None) ::
          (@^mTimeReg, existT _ (SyntaxKind Data) (Some (SyntaxConst (wzero Xlen)))) ::
          (@^mTimeCmpReg, existT _ (SyntaxKind Data) (Some (SyntaxConst (wzero Xlen)))) ::
          (@^mtiReg, existT _ (SyntaxKind Bool) (Some (SyntaxConst true))) ::
          nil
      else nil.

  Definition specBaseMod: BaseModule := BaseMod specRegs specRules [].

  Ltac conjunctionRepeatConstructors :=
    match goal with
    | |- ?A /\ ?B => constructor; conjunctionRepeatConstructors
    | |- _ => idtac
    end.

  Local Ltac constructor_simpl :=
    econstructor; eauto; simpl; unfold not; intros.

  Ltac murali := match goal with
                 | |- @WfBaseModule_new _ _ => unfold WfBaseModule_new
                 | |- @WfMod_new _ _ => constructor_simpl
                 | |- _ /\ _ => constructor_simpl
                 | |- @WfActionT_new _ _ _ (convertLetExprSyntax_ActionT ?e) => apply WfLetExprSyntax_new
                 | |- @WfActionT_new _ _ _ _ => constructor_simpl
                 | |- NoDup _ => constructor_simpl
                 | H: _ \/ _ |- _ => destruct H; subst; simpl
                 | |- forall _, _ => intros
                 | |- _ -> _ => intros 
                 | H: In _ (getAllMethods _) |- _ => simpl in H;inversion H;subst;clear H;simpl
                 | |- _ => unfold lookup; simpl; repeat rewrite strip_pref
                 end; unfold lookup; simpl; repeat rewrite strip_pref; simpl.

  (*
  Theorem WfSpecDecRule: forall ie ty, WfActionT_new specRegs (specDecExecRule scrList csrList ty ie).
  Proof.
    cbv [specRegs specDecExecRule handleException]; intros.
    murali.
    unfold lookup; simpl; repeat rewrite strip_pref; simpl.
    - 
    cbv [lookup find fst snd].
    rewrite ?strip_pref.
    match goal with
    | |- context [String.eqb ?P ?Q] => cbv [P Q String.eqb Ascii.eqb Bool.eqb]
    end.
    discharge_wf_new.
    - murali.
    - 
    test.
  Qed.

    discharge_wf_new.
  Theorem WfSpecBaseMod: WfBaseModule_new type specBaseMod.
  Proof.
    cbv [WfBaseModule_new getRegisters getRules getMethods specBaseMod specRules specRegs
           specTimerIncAndInterruptSetRule
           specTimerInterruptTakeRule specInstBoundsExceptionRule specInstIllegalExceptionRule specDecExecRule].
    conjunctionRepeatConstructors.
    - cbn [WfRules snd]; conjunctionRepeatConstructors.
      + destruct hasTrap; discharge_wf_new.
      + cbv [handleException]; destruct hasTrap.
        * discharge_wf_new.
      + 
      + 
    - constructor.
    - constructor.
    - destruct hasTrap; cbv [map fst];
        apply (NoDup_map_inv (rmStringPrefix (String.length (procName ++ "_"))%string)); cbv [map];
        rewrite ?rmAppend; discharge_wf_new.
    - destruct hasTrap; cbv [map fst specInstEntries instName mkLdInst mkStInst mkBranchInst mkCsrEntry];
        cbn [append]; discharge_wf_new.
  Admitted.
*)
End Prefix.
