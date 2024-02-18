Require Import Kami.AllNotations.
Require Import ProcKami.Cheriot.Types ProcKami.Cheriot.Config ProcKami.Cheriot.InstSpec ProcKami.Cheriot.SpecRun.

Section CoreConfig.
  Variable name : string.
  Variable hasTrap: bool.
  Definition config := procParams name.
  
End CoreConfig.
