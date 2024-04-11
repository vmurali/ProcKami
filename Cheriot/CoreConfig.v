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
      (@^"specDecExecRule", fun ty => specDecExecRule scrList csrList ty specInstEntries) :: nil.

  Definition specRegs : list RegInitT :=
    (@^pcCapReg, existT _ (SyntaxKind Cap) (Some (SyntaxConst (convTypeToConst pcCapInit)))) ::
      (@^pcValReg, existT _ (SyntaxKind Addr) (Some (SyntaxConst pcValInit))) ::
      (@^prevPcValReg, existT _ (SyntaxKind (Maybe Addr)) (Some (SyntaxConst (getDefaultConst (Maybe Addr))))) ::
      (@^regsArray, existT _ _ (Some (SyntaxConst (@convTypeToConst (Array NumRegs FullCapWithTag) regsInit)))) ::
      (@^memArray, existT _ _ (Some (SyntaxConst (@convTypeToConst (Array NumMemBytes FullCapWithTag)
                                                    memInit)))) ::
      (@^pcCountNReg, existT _ _ (Some (NativeConst (fun (pc: type Addr) => 0)))) ::
      if hasTrap
      then
        (@^mtccReg,
          existT _ (SyntaxKind FullCapWithTag)
            (Some (SyntaxConst
                     (convTypeToConst
                        (evalExpr (STRUCT { "tag" ::= Const type true;
                                            "cap" ::= Const _ (convTypeToConst mtccCap);
                                            "val" ::= Const _ mtccVal})))))) ::
          (@^mtdcReg,
            existT _ (SyntaxKind FullCapWithTag)
              (Some (SyntaxConst
                       (convTypeToConst
                          (evalExpr (STRUCT { "tag" ::= Const type true;
                                              "cap" ::= Const _ (convTypeToConst mtdcCap);
                                              "val" ::= Const _ mtccVal})))))) ::
          (@^mScratchCReg,
            existT _ (SyntaxKind FullCapWithTag)
              (Some (SyntaxConst
                       (convTypeToConst
                          (evalExpr (STRUCT { "tag" ::= Const type true;
                                              "cap" ::= Const _ (convTypeToConst mScratchCCap);
                                              "val" ::= Const _ (wzero Xlen)})))))) ::
          (@^mepccReg, existT _ (SyntaxKind FullCapWithTag) (Some (SyntaxConst (getDefaultConst FullCapWithTag)))) ::
          (@^mStatusReg, existT _ (SyntaxKind Data) (Some (SyntaxConst (wzero Xlen)))) ::
          (@^mCauseReg, existT _ (SyntaxKind Data) None) ::
          (@^mtValReg, existT _ (SyntaxKind Data) None) ::
          (@^mTimeReg, existT _ (SyntaxKind Data) (Some (SyntaxConst (wzero Xlen)))) ::
          (@^mTimeCmpReg, existT _ (SyntaxKind Data) (Some (SyntaxConst (wzero Xlen)))) ::
          (@^mtiReg, existT _ (SyntaxKind Bool) (Some (SyntaxConst true))) ::
          nil
      else nil.

  Definition specBaseMod: BaseModule := BaseMod specRegs specRules [].

  Theorem WfSpecDecExecRule: forall ty, WfActionT specRegs (specDecExecRule scrList csrList ty specInstEntries).
  Proof.
    cbv [specRegs specDecExecRule handleException MemSpec.storeReqSpec MemSpec.instReqSpec MemSpec.loadReqSpec
           readRegs writeRegsPred];
      intros.
    destruct hasTrap;
      cbn [redAction fold_right Lib.redActionHelp scrList csrList scrRegInfo csrRegInfo
             map filter isSystemCsr negb regName];
      repeat dischargeWfActionT_specific.
  Qed.

  Theorem WfSpecTimerIncAndInterruptSetRule: forall ty, WfActionT specRegs (specTimerIncAndInterruptSetRule ty).
  Proof.
    cbv [specRegs specTimerIncAndInterruptSetRule handleException]; intros.
    destruct hasTrap; repeat dischargeWfActionT.
  Qed.

  Ltac instEntriesNoDup :=
    cbv [specInstEntries]; destruct hasTrap; cbn [map fst instName mkLdInst mkStInst mkBranchInst mkCsrEntry append];
    commonPrefixNoDup.

  Theorem NoDupSpecRules: NoDup (map fst specRules).
  Proof.
    cbn [specRules map fst].
    instEntriesNoDup.
  Qed.
  
  Theorem WfSpecBaseMod: WfBaseModule type specBaseMod.
  Proof.
    cbv [WfBaseModule getRegisters getRules getMethods specBaseMod].
    repeatConj.
    - cbv [specRules]; cbn [In]; let rule := fresh "rule" in intro rule; intros.
      repeat match goal with
             | H: _ \/ _ |- _ => destruct H
             | H: _ /\ _ |- _ => destruct H
             | H: exists x, _ |- _ => destruct H
             | H: _ = rule |- _ => rewrite <- H; clear H rule;
                                   cbn [snd]
             | H: False |- _ => exfalso; assumption
             end.
      + apply WfSpecTimerIncAndInterruptSetRule.
      + apply WfSpecDecExecRule.
    - cbv [In].
      intros; tauto.
    - constructor.
    - cbv [specRegs]; instEntriesNoDup.
    - apply NoDupSpecRules.
  Qed.
End Prefix.
