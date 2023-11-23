Require Import Kami.AllNotations ProcKami.Cheriot.Lib ProcKami.Cheriot.Types ProcKami.Cheriot.DecExec.

Section CsrScr.
  Context `{procParams: ProcParams}.

  (* TODO: See how these can be not hardcoded. Also see how SCR inst entries can be made better *)
  Definition MStatusAddr := (snd immField) 'h"300".

  Definition csrs : list (RegInfo (snd immField) Data) := [
      Build_RegInfo (_ 'h"C01") "time" (Some (SyntaxConst Default));
      Build_RegInfo (_ 'h"C81") "timeh" (Some (SyntaxConst Default));
      Build_RegInfo MStatusAddr "mstatus" (Some (SyntaxConst Default));
      Build_RegInfo (_ 'h"342") "mcause" None;
      Build_RegInfo (_ 'h"343") "mtval" None ].
  
  Definition isValidCsrs ty (inst : Inst @# ty) :=
    Kor (map (fun csr => (imm inst == Const ty (regAddr csr))%kami_expr) csrs).

  (* TODO: See how these can be not hardcoded. Also see how SCR inst entries can be made better *)
  Definition MepccAddr := 31.
  
  Definition scrs : list (RegInfo (snd rs2FixedField) FullCapWithTag) := [
      Build_RegInfo ($28) "MTCC" (Some (SyntaxConst Default));
      Build_RegInfo ($29) "MTDC" (Some (SyntaxConst Default));
      Build_RegInfo ($30) "MScratchC" None;
      Build_RegInfo ($MepccAddr) "MEPCC" None ].

  Definition isValidScrs ty (inst : Inst @# ty) :=
    Kor (map (fun csr => (rs2Fixed inst == Const ty (regAddr csr))%kami_expr) scrs).
End CsrScr.
