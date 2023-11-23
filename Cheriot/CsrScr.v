Require Import Kami.AllNotations ProcKami.Cheriot.Types ProcKami.Cheriot.DecExec.

Section CsrScr.
  Context `{procParams: ProcParams}.

  (* TODO: See how these can be not hardcoded. Also see how SCR inst entries can be made better *)
  Definition MStatusAddr := (snd immField) 'h"300".

  Definition csrs : list (RegInfo (snd immField)) := [
      Build_RegInfo (_ 'h"C01") ("time", existT _ (SyntaxKind Data) (Some (SyntaxConst Default)));
      Build_RegInfo (_ 'h"C81") ("timeh", existT _ (SyntaxKind Data) (Some (SyntaxConst Default)));
      Build_RegInfo MStatusAddr ("mstatus", existT _ (SyntaxKind Data) (Some (SyntaxConst Default)));
      Build_RegInfo (_ 'h"342") ("mcause", existT _ (SyntaxKind Data) None);
      Build_RegInfo (_ 'h"343") ("mtval", existT _ (SyntaxKind Data) None) ].
  
  Definition isValidCsrs ty (inst : Inst @# ty) :=
    Kor (map (fun csr => (imm inst == Const ty (regAddress csr))%kami_expr) csrs).

  (* TODO: See how these can be not hardcoded. Also see how SCR inst entries can be made better *)
  Definition MepccAddr := 31.
  
  Definition scrs : list (RegInfo (snd rs2FixedField)) := [
      Build_RegInfo ($28) ("MTCC", existT _ (SyntaxKind FullCapWithTag) (Some (SyntaxConst Default)));
      Build_RegInfo ($29) ("MTDC", existT _ (SyntaxKind FullCapWithTag) (Some (SyntaxConst Default)));
      Build_RegInfo ($30) ("MScratchC", existT _ (SyntaxKind FullCapWithTag) None);
      Build_RegInfo ($MepccAddr) ("MEPCC", existT _ (SyntaxKind FullCapWithTag) (Some (SyntaxConst Default))) ].

  Definition isValidScrs ty (inst : Inst @# ty) :=
    Kor (map (fun csr => (rs2Fixed inst == Const ty (regAddress csr))%kami_expr) scrs).
End CsrScr.
