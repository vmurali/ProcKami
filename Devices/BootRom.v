Require Import Kami.AllNotations.

Require Import ProcKami.FU.
Require Import ProcKami.Device.
Require Import ProcKami.MemOpsFuncs.

Require Import StdLibKami.Router.Ifc.

Section device.
  Context (procParams: ProcParams).

  Local Definition LgMemSz := 12.

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Definition bootRom := createDevice
    {| baseName := "bootRom";
       baseIo := true;
       basePmas :=  map
                (fun width
                 => {|
                     pmaWidth      := width;
                     pmaReadable   := true;
                     pmaWriteable  := false;
                     pmaExecutable := true;
                     pmaMisaligned := true;
                   |})
                [0; 1; 2; 3];
       baseAmo := AmoNone;
       baseRegFiles := {| rfIsWrMask := true;
                          rfNum := Rlen_over_8;
                          rfDataArray := "bootRomFile";
                          rfRead := Async ["bootRomRead"];
                          rfWrite := "bootRomWrite";
                          rfIdxNum := (Nat.pow 2 LgMemSz);
                          rfData := (Bit 8);
                          rfInit := RFFile true true "boot_rom" 0 (Nat.pow 2 LgMemSz) (fun _ => wzero _) |} :: nil;
       baseRegs := makeModule_regs (Register "bootRomReadReg" : Array Rlen_over_8 (Bit 8) <- Default)%kami;
       write := (fun _ _ => Ret $$false);
       readReq := (fun ty addr =>
                     Call val: Array Rlen_over_8 (Bit 8) <-
                                 "bootRomRead" (SignExtendTruncLsb LgMemSz addr : Bit LgMemSz);
                     Write "bootRomReadReg" : (Array Rlen_over_8 (Bit 8)) <- #val;
                     Retv);
       readRes := (fun ty => (Read readData : Array Rlen_over_8 (Bit 8) <- "bootRomReadReg";
                              Ret ((Valid (pack #readData)): Maybe Data @# ty))); |}.
End device.
