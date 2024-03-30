Require Import Kami.AllNotations.
Require Import ProcKami.Cheriot.Lib ProcKami.Cheriot.Types ProcKami.Cheriot.InstSpec ProcKami.Cheriot.RunSpec.

Section Prefix.
  Context `{coreConfigParams: CoreConfigParams}.
  Instance memParamsInst: MemParams := memParams.

  Local Notation "@^ x" := (procName ++ "_" ++ x)%string (at level 0).
  Local Open Scope kami_expr.

  Definition specRules : list (forall ty, ActionT ty Void) :=
    (fun ty => specInstBoundsExceptionRule ty scrList csrList) ::
      (fun ty => specInstIllegalExceptionRule ty scrList csrList specInstEntries) ::
      map (fun ie ty => specDecExecRule ty scrList csrList ie) specInstEntries.

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
          (@^mtValReg, existT _ (SyntaxKind Data) None) :: nil
      else nil.
End Prefix.
