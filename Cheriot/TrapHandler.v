Require Import Kami.AllNotations ProcKami.Cheriot.InstAssembly ProcKami.Cheriot.Types.

(* Doesn't contain reset code *)
Section TrapHandler.
  Variable TimerQuantum: word (Xlen - 1).
  Variable NumProcesses: word (Xlen / 2).

  (* MTDC points to trap_handler_data, whose layout is as follows:
   * Cap to Timer (8 bytes)
   * Cap to TimeCmp (8 bytes)
   * Cap to current proc (8 bytes)
   * proc0 Regs ((NumRegs+1) * 8 bytes)
   * proc1 Regs ((NumRegs+1) * 8 bytes)
   * ...
   * proc_pred_n Regs ((NumRegs+1) * 8 bytes)
   *)
  Local Open Scope cheriot_assembly_scope.

  Definition setTimeCmp (mtdcAddr tmp: RegScrName) :=
    let mTimeAddr := tmp in
    let mTimeCmpAddr := mtdcAddr in
    ( clc mTimeAddr, 0#[mtdcAddr] ;;
      clw tmp, 0#[mTimeAddr] ;;
      addi tmp, tmp, wordVal _ TimerQuantum ;;
      clc mTimeCmpAddr, 8#[mtdcAddr] ;;
      csw 0#[mTimeCmpAddr], tmp
    ).

  Definition saveRegsFrom2AddrInC1 :=
    ( csc  16#[c1],  c2 ;;
      csc  24#[c1],  c3 ;;
      csc  32#[c1],  c4 ;;
      csc  40#[c1],  c5 ;;
      csc  48#[c1],  c6 ;;
      csc  56#[c1],  c7 ;;
      csc  64#[c1],  c8 ;;
      csc  72#[c1],  c9 ;;
      csc  80#[c1], c10 ;;
      csc  88#[c1], c11 ;;
      csc  96#[c1], c12 ;;
      csc 104#[c1], c13 ;;
      csc 112#[c1], c14 ;;
      csc 120#[c1], c15 ;;
      csc 128#[c1], c16 ;;
      csc 136#[c1], c17 ;;
      csc 144#[c1], c18 ;;
      csc 152#[c1], c19 ;;
      csc 160#[c1], c20 ;;
      csc 168#[c1], c21 ;;
      csc 176#[c1], c22 ;;
      csc 184#[c1], c23 ;;
      csc 192#[c1], c24 ;;
      csc 200#[c1], c25 ;;
      csc 208#[c1], c26 ;;
      csc 216#[c1], c27 ;;
      csc 224#[c1], c28 ;;
      csc 232#[c1], c29 ;;
      csc 240#[c1], c30 ;;
      csc 248#[c1], c31 ).

  (* tmp can be any register except c0/c1 *)
  Definition saveCurrentContext (tmp: RegScrName) :=
    ( cspecialw mscratchc, c1 ;;
      cspecialr c1, mtdc ;;
      clc c1, 16#[c1] ;;
      saveRegsFrom2AddrInC1 ;;
      cspecialr tmp, mepcc ;;
      csc 0#[c1], tmp ;;
      cspecialr tmp, mscratchc ;;
      csc 8#[c1], tmp ;;
      csrr tmp, mstatus ;;
      csw 256#[c1], tmp ).

  Definition loadRegsFrom4AddrInC1 :=
    ( clc  c4,  32#[c1] ;;
      clc  c5,  40#[c1] ;;
      clc  c6,  48#[c1] ;;
      clc  c7,  56#[c1] ;;
      clc  c8,  64#[c1] ;;
      clc  c9,  72#[c1] ;;
      clc c10,  80#[c1] ;;
      clc c11,  88#[c1] ;;
      clc c12,  96#[c1] ;;
      clc c13, 104#[c1] ;;
      clc c14, 112#[c1] ;;
      clc c15, 120#[c1] ;;
      clc c16, 128#[c1] ;;
      clc c17, 136#[c1] ;;
      clc c18, 144#[c1] ;;
      clc c19, 152#[c1] ;;
      clc c20, 160#[c1] ;;
      clc c21, 168#[c1] ;;
      clc c22, 176#[c1] ;;
      clc c23, 184#[c1] ;;
      clc c24, 192#[c1] ;;
      clc c25, 200#[c1] ;;
      clc c26, 208#[c1] ;;
      clc c27, 216#[c1] ;;
      clc c28, 224#[c1] ;;
      clc c29, 232#[c1] ;;
      clc c30, 240#[c1] ;;
      clc c31, 248#[c1] ).

  Definition loadRegsFrom2To3AddrInC1 :=
    ( clc  c2,  16#[c1] ;;
      clc  c3,  24#[c1] ).

  (* c1 already contains new context; c2 already contains mtdc; tmp is c3;
     final regs are based on new context *)
  Definition loadContextSetTimeCmpMRet :=
    let mtdcAddr := c2 in
    let tmp := c3 in
    ( loadRegsFrom4AddrInC1 ;;
      setTimeCmp mtdcAddr c3 ;;
      clw tmp, 256#[c1] ;;
      csrw mstatus, tmp ;;
      clc tmp, 0#[c1] ;;
      cspecialw mepcc, tmp ;;
      loadRegsFrom2To3AddrInC1 ;;
      clc c1, 8#[c1] ;;
      mret ).

  (* mtdcAddr contains mtdc's address finally; c1 contains new context finally;
     new context is stored in 16#[mtdc] finally; tmp is clobbered *)
  Definition advanceContext (mtdcAddr tmp: RegScrName) :=
    ( cspecialr mtdcAddr, mtdc ;;
      clc c1, 16#[mtdcAddr] ;;
      cincaddrimm c1, c1, (8*(Z.of_nat NumRegs+1)) ;;
      cincaddrimm tmp, mtdcAddr, (24+((wordVal _ NumProcesses)*(8*(Z.of_nat NumRegs+1)))) ;;
      LOCAL LSkip;
      bge c1, tmp, LSkip ;;
      cincaddrimm c1, mtdcAddr, 24 ;;
    LSkip :;;
      csc 16#[mtdcAddr], c1 ).

  Definition trapHandler :=
    ( saveCurrentContext c2 ;;
      advanceContext c2 c3 ;;
      loadContextSetTimeCmpMRet ).
End TrapHandler.
