Require Import Kami.AllNotations.
Require Import ProcKami.Cheriot.Lib ProcKami.Cheriot.Types ProcKami.Cheriot.CoreConfig.
Require Import ProcKami.Cheriot.InstSpec ProcKami.Cheriot.SpecRun.

Section SpecInstance.
  Variable name: string.
  Variable LgNumMemBytesVal: nat.
  Variable memInitVal: Fin.t (Nat.pow 2 LgNumMemBytesVal * 8) -> word 8.
  Variable regsInitVal: Fin.t 32 -> type FullCapWithTagKind.
  Variable pcCapInitVal: word 32.
  Variable pcCapValidThm: PcCapValid capAccessorsInit pcCapInitVal.
  Variable pcValInitVal: word 32.
  Variable pcValValidThm: truncLsb pcValInitVal = ZToWord 2 0.
  Local Notation "@^ x" := (name ++ "_" ++ x)%string (at level 0).

  Instance procParams: ProcParams :=
    CoreConfig.procParams name LgNumMemBytesVal memInitVal regsInitVal pcCapValidThm pcValValidThm false.

  Definition getInstEntrySpec (fe: FuncEntry) : list (InstEntry FullOutput) :=
    map (fun ie => {|instName := instName ie;
                     uniqId := uniqId ie;
                     immEncoder := immEncoder ie;
                     spec := fun ty pcc inst cs1 cs2 scr csr =>
                               (LETE val <- spec ie pcc inst cs1 cs2 scr csr;
                                localFunc fe #val)%kami_expr;
                     instProperties := instProperties ie;
                     goodInstEncode := goodInstEncode ie;
                     goodImmEncode := goodImmEncode ie |}) (insts fe).

  Definition specInstEntries := concat (map getInstEntrySpec specFuncUnits).

  Definition specRules : list (forall ty, ActionT ty Void) :=
    specInstBoundsException ::
      (fun ty => specInstIllegalException ty specInstEntries) ::
      map (fun ie ty => specDecExecRule ty scrList csrList ie) specInstEntries.

  Definition specRegs : list RegInitT :=
    (pcCapReg, existT _ (SyntaxKind (Bit CapSz)) (Some (SyntaxConst pcCapInitVal))) ::
      (pcValReg, existT _ (SyntaxKind Addr) (Some (SyntaxConst pcValInitVal))) ::
      (prevPcCapReg, existT _ (SyntaxKind (Bit CapSz)) (Some (SyntaxConst $0))) ::
      (prevPcValReg, existT _ (SyntaxKind Addr) (Some (SyntaxConst $0))) ::
      (regsArray, existT _ _ (Some (SyntaxConst (@convTypeToConst (Array 32 FullCapWithTagKind) regsInitVal)))) ::
      (memArray, existT _ _ (Some (SyntaxConst (@convTypeToConst (Array (NumMemBytes * NumBanks) (Bit 8))
                                                  memInitVal)))) ::
      (map (fun x => (regName (scrRegInfo x), existT _ _ (regInit (scrRegInfo x)))) scrList) ++
      (map (fun x => (regName (csrRegInfo x), existT _ _ (regInit (csrRegInfo x)))) csrList).
End SpecInstance.
