Require Import Kami.AllNotations.

Require Import ProcKami.FU.
Require Import ProcKami.Device.
Require Import ProcKami.MemOpsFuncs.

Require Import StdLibKami.Router.Ifc.

Section device.
  Context (procParams: ProcParams).

  Local Definition LgMemSz := 20.

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Definition pMem := createDevice
    {| baseName := "pMem";
       baseIo := true;
       basePmas := pmas_default;
       baseRegFiles := {| rfIsWrMask := true;
                          rfNum := Rlen_over_8;
                          rfDataArray := "pMemFile";
                          rfRead := Async ["pMemRead"];
                          rfWrite := "pMemWrite";
                          rfIdxNum := (Nat.pow 2 LgMemSz);
                          rfData := (Bit 8);
                          rfInit := RFFile true true "testfile" 0 (Nat.pow 2 LgMemSz) (fun _ => wzero _) |} :: nil;
       baseRegs := makeModule_regs (Register "pMemReadReg" : Array Rlen_over_8 (Bit 8) <- Default)%kami;
       baseAmo := AmoNone;
       write := (fun ty req =>
                   LET writeRq
                   :  WriteRqMask LgMemSz Rlen_over_8 (Bit 8)
                      <- (STRUCT {
                              "addr" ::= SignExtendTruncLsb LgMemSz (req @% "addr");
                              "data" ::= req @% "data";
                              "mask" ::= req @% "mask"
                            } : WriteRqMask LgMemSz Rlen_over_8 (Bit 8) @# ty);
                   Call "pMemWrite" (#writeRq: _);
                   Ret $$true);
       readReq := (fun ty addr =>
                     Call val : Array Rlen_over_8 (Bit 8) <-
                                  "pMemRead" (SignExtendTruncLsb LgMemSz addr : Bit LgMemSz);
                     Write "pMemReadReg" : Array Rlen_over_8 (Bit 8) <- #val;
                     Retv);
       readRes := (fun ty => Read readData : Array Rlen_over_8 (Bit 8) <- "pMemReadReg";
                             Ret ((Valid (pack #readData)): Maybe Data @# ty)); |}.
End device.
