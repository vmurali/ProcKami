Require Import Kami.AllNotations ProcKami.Cheriot.InstAssembly ProcKami.Cheriot.Types.

Section TrapHandler.
  Variable startAlign: Z.
  Variable TimerQuantum: word 12.
  Variable NumProcesses: word 12.

  (* MTDC points to trap_handler_data, whose layout is as follows:
   * Cap to Timer (8 bytes)
   * Cap to TimeCmp (8 bytes)
   * Cap to current proc (8 bytes)
   * proc0 Regs (NumRegs * 8 bytes)
   * proc1 Regs (NumRegs * 8 bytes)
   * ...
   * proc_pred_n Regs (NumRegs * 8 bytes)
   *)
  Local Open Scope cheriot_assembly_scope.

  Definition getRegIdUnsafe (z: Z) := match getRegNameOpt z with
                                      | Some name => name
                                      | None => zero
                                      end.

  Definition filteredRegsZ (l: list RegName) :=
    filter (fun z: Z => negb (existsb (fun r => Z.eqb z (getRegIdZ r)) l)) (map Z.of_nat (seq 1 31)).

  (* curr refers to the register storing the current context cap *)
  Definition saveAllRegsExcept (curr: RegName) (l: list RegName) :=
    fold_right (fun z rest => csc (z * 8)#[curr], (getRegIdUnsafe z) ;; rest) ProgSkip (filteredRegsZ (curr :: l)).

  Definition loadAllRegsExcept (curr: RegName) (l: list RegName) :=
    fold_right (fun z rest => clc (getRegIdUnsafe z),  (z * 8)#[curr] ;; rest) ProgSkip (filteredRegsZ (curr :: l)).

  (* curr will finally hold current context in the end *)
  Definition saveCurrentContext (curr tmp: RegName)
    (pf: isSameReg curr tmp = false) :=
    ( cspecialw mscratchc, curr ;; (* storing current value of curr register into mscratchc *)
      cspecialr curr, mtdc ;; (* storing mtdc cap into curr register *)
      clc curr, 16#[curr] ;; (* Current processor offset into curr register, it no longer has mtdc address *)
      saveAllRegsExcept curr [] ;;
      cspecialr tmp, mscratchc ;;
      csc ((getRegIdZ curr) * 8)#[curr], tmp ;; (* Store the prev value of curr register, which was in mscratch *)
      cspecialr tmp, mepcc ;;
      csc 0#[curr], tmp (* Store mepcc in slot for 0 register of current context *) ).

  Definition MtdcTotalSize := (24 + ((wordVal _ NumProcesses) * ((Z.of_nat NumRegs) * 8)))%Z.

  (* mtdcAddr will contain mtdc cap in the end, curr contains current context in the beginning,
     curr will contain next context cap in the end *)
  Definition advanceContext (mtdcAddr curr tmp: RegName)
    (pf1: isSameReg mtdcAddr curr = false)
    (pf2: isSameReg curr tmp = false)
    (pf3: isSameReg mtdcAddr tmp = false) :=
    ( cspecialr mtdcAddr, mtdc ;;
      cincaddrimm curr, curr, ((Z.of_nat NumRegs) * 8) ;;
      lui tmp, %hi(MtdcTotalSize) ;;
      addi tmp, tmp, %lo(MtdcTotalSize) ;;
      cincaddr tmp, mtdcAddr, tmp ;;
      LOCAL LSkip;
      blt curr, tmp, LSkip ;;
      cincaddrimm curr, mtdcAddr, 24 ;;
    LSkip :;;
      csc 16#[mtdcAddr], curr ).

  Definition TimerQuantumZ := wordVal _ TimerQuantum.

  (* mtdcAddr register contains mtdc cap initially, and clobbered in the end *)
  Definition setTimeCmp (mtdcAddr tmp: RegName)
    (pf: isSameReg mtdcAddr tmp = false) :=
    ( clc tmp, 0#[mtdcAddr] ;;
      clw tmp, 0#[tmp] ;;
      addi tmp, tmp, TimerQuantumZ ;;
      clc mtdcAddr, 8#[mtdcAddr] ;;
      csw 0#[mtdcAddr], tmp
    ).

  (* mtdcAddr contains mtdc cap, curr contains current context cap in the beginning *)
  Definition loadContextSetTimeCmpMRet (mtdcAddr curr tmp: RegName)
    (pf1: isSameReg mtdcAddr curr = false)
    (pf2: isSameReg curr tmp = false)
    (pf3: isSameReg mtdcAddr tmp = false) :=
    ( loadAllRegsExcept curr [mtdcAddr; tmp] ;;
      clc tmp, 0#[curr] ;;
      cspecialw mepcc, tmp ;;
      setTimeCmp mtdcAddr tmp pf3 ;;
      clc tmp, ((getRegIdZ tmp) * 8)#[curr] ;;
      clc mtdcAddr, ((getRegIdZ mtdcAddr) * 8)#[curr] ;;
      clc curr, ((getRegIdZ curr) * 8)#[curr] ;;
      mret ).

  Definition trapHandler (mtdcAddr curr tmp: RegName)
    (pf1: isSameReg mtdcAddr curr = false)
    (pf2: isSameReg curr tmp = false)
    (pf3: isSameReg mtdcAddr tmp = false) :=
    ( saveCurrentContext curr tmp pf2 ;;
      advanceContext mtdcAddr curr tmp pf1 pf2 pf3 ;;
      loadContextSetTimeCmpMRet mtdcAddr curr tmp pf1 pf2 pf3 ).

  Definition trapHandlerInsts :=
    ltac:(let y := eval unfold trapHandler, saveCurrentContext, advanceContext,
              loadContextSetTimeCmpMRet, setTimeCmp, saveAllRegsExcept, loadAllRegsExcept,
              getInstBytes, getAddrMap, setLabel, getInstBytesResolved, getInstructionRel, instEncoder, splitInst in
          (getInstBytes startAlign (trapHandler c1 c2 c3 eq_refl eq_refl eq_refl)) in
            let z := eval simpl in y in exact z).

  Definition trapHandlerSize := ltac:(let x := eval simpl in
                                      (Z.of_nat (length trapHandlerInsts)) in exact x).
End TrapHandler.
