Require Import Kami.AllNotations.

Require Import ProcKami.Cheriot.Lib ProcKami.Cheriot.Types ProcKami.Cheriot.InstSpec ProcKami.Cheriot.RunSpec.
Require Import ProcKami.Cheriot.Tactics.

Section Prefix.
  Context `{coreConfigParams: CoreConfigParams}.
  Instance memParamsInst: MemParams := memParams.

  Local Notation "@^ x" := ((procName ++ "_") ++ x)%string (at level 0).
  Local Open Scope kami_expr.

  Definition specRules : list RuleT :=
    (@^"specTimerIncAndInterruptSetRule", specTimerIncAndInterruptSetRule) ::
      (@^"specTimerInterruptTakeRule", specTimerInterruptTakeRule scrList csrList) ::
      (@^"specInstBoundsExceptionRule", specInstBoundsExceptionRule scrList csrList) ::
      (@^"specInstIllegalExceptionRule", fun ty => specInstIllegalExceptionRule scrList csrList ty specInstEntries) ::
      map (fun ie => (@^(append "specDecExecRule_" (instName ie)), fun ty => specDecExecRule scrList csrList ty ie))
      specInstEntries.

  Definition specRegs : list RegInitT :=
    (@^pcCapReg, existT _ (SyntaxKind Cap) (Some (SyntaxConst (convTypeToConst pcCapInit)))) ::
      (@^pcValReg, existT _ (SyntaxKind Addr) (Some (SyntaxConst (wcombine pcValInit (wzero 2))))) ::
      (@^regsArray, existT _ _ (Some (SyntaxConst (@convTypeToConst (Array NumRegs FullCapWithTag) regsInit)))) ::
      (@^memArray, existT _ _ (Some (SyntaxConst (@convTypeToConst (Array NumMemBytes FullCapWithTag)
                                                    memInit)))) ::
      if hasTrap
      then
        (@^mtccReg,
          existT _ (SyntaxKind FullCapWithTag)
            (Some (SyntaxConst
                     (convTypeToConst
                        (evalExpr (STRUCT { "tag" ::= Const type true;
                                            "cap" ::= ExecRootCapExpr type;
                                            "val" ::= Const _ (wcombine mtccValInit (wzero 2))})))))) ::
          (@^mtdcReg,
            existT _ (SyntaxKind FullCapWithTag)
              (Some (SyntaxConst
                       (convTypeToConst
                          (evalExpr (STRUCT { "tag" ::= Const type true;
                                              "cap" ::= DataRootCapExpr type;
                                              "val" ::= Const _ (wcombine mtdcValInit (wzero 2))})))))) ::
          (@^mScratchCReg,
            existT _ (SyntaxKind FullCapWithTag)
              (Some (SyntaxConst
                       (convTypeToConst
                          (evalExpr (STRUCT { "tag" ::= Const type true;
                                              "cap" ::= SealRootCapExpr type;
                                              "val" ::= Const _ (wzero Xlen)})))))) ::
          (@^mepccReg, existT _ (SyntaxKind FullCapWithTag) (Some (SyntaxConst (getDefaultConst FullCapWithTag)))) ::
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

  Theorem WfSpecDecExecRule: forall ie ty, WfActionT specRegs (specDecExecRule scrList csrList ty ie).
  Proof.
    cbv [specRegs specDecExecRule handleException]; intros.
    destruct hasTrap; repeat dischargeWfActionT.
  Qed.

  Theorem WfSpecTimerIncAndInterruptSetRule: forall ty, WfActionT specRegs (specTimerIncAndInterruptSetRule ty).
  Proof.
    cbv [specRegs specTimerIncAndInterruptSetRule handleException]; intros.
    destruct hasTrap; repeat dischargeWfActionT.
  Qed.

  Theorem WfSpecTimerInterruptTakeRule: forall ty, WfActionT specRegs (specTimerInterruptTakeRule scrList csrList ty).
  Proof.
    cbv [specRegs specTimerInterruptTakeRule handleException]; intros.
    destruct hasTrap; repeat dischargeWfActionT.
  Qed.

  Theorem WfSpecInstBoundsExceptionRule:
    forall ty, WfActionT specRegs (specInstBoundsExceptionRule scrList csrList ty).
  Proof.
    cbv [specRegs specInstBoundsExceptionRule handleException]; intros.
    destruct hasTrap; repeat dischargeWfActionT.
  Qed.

  Theorem WfSpecInstIllegalExceptionRule:
    forall ty, WfActionT specRegs (specInstIllegalExceptionRule scrList csrList ty specInstEntries).
  Proof.
    cbv [specRegs specInstIllegalExceptionRule handleException]; intros.
    destruct hasTrap; repeat dischargeWfActionT.
  Qed.

  Ltac instEntriesNoDup :=
    cbv [specInstEntries]; destruct hasTrap; cbn [map fst instName mkLdInst mkStInst mkBranchInst mkCsrEntry append];
    commonPrefixNoDup.

  Theorem NoDupSpecRules: NoDup (map fst specRules).
  Proof.
    cbn [specRules map fst].
    rewrite map_map.
    instEntriesNoDup.
  Qed.
  
  Theorem WfSpecBaseMod: WfBaseModule type specBaseMod.
  Proof.
    cbv [WfBaseModule getRegisters getRules getMethods specBaseMod].
    repeatConj.
    - cbv [specRules]; cbn [In]; let rule := fresh "rule" in intro rule; rewrite in_map_iff; intros.
      repeat match goal with
             | H: _ \/ _ |- _ => destruct H
             | H: _ /\ _ |- _ => destruct H
             | H: exists x, _ |- _ => destruct H
             | H: _ = rule |- _ => rewrite <- H; clear H rule;
                                   cbn [snd]
             end.
      + apply WfSpecTimerIncAndInterruptSetRule.
      + apply WfSpecTimerInterruptTakeRule.
      + apply WfSpecInstBoundsExceptionRule.
      + apply WfSpecInstIllegalExceptionRule.
      + apply WfSpecDecExecRule.
    - cbv [In].
      intros; tauto.
    - constructor.
    - cbv [specRegs]; instEntriesNoDup.
    - apply NoDupSpecRules.
  Qed.
End Prefix.
