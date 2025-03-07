Require Import Kami.AllNotations.
Require Import ProcKami.Cheriot.Types.
Require Import ProcKami.Cheriot.DecExec ProcKami.Cheriot.MemSpec.

Section Run.
  Context `{coreConfigParams: CoreConfigParams}.
  Instance memParamsInst: MemParams := memParams.

  Variable scrs: list ScrReg.
  Variable csrs: list CsrReg.

  Variable ty: Kind -> Type.

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Let scrRegInfos := if hasTrap then map scrRegInfo scrs else [].
  Let csrRegInfos := map csrRegInfo (if hasTrap then csrs else filter (fun csrReg => negb (isSystemCsr csrReg)) csrs).

  Local Notation "@^ x" := ((procName ++ "_") ++ x)%string (at level 0).

  Definition handleException
    (mtiReset: Bool @# ty)
    (currPcVal: Addr @# ty)
    (newPcVal: Addr @# ty)
    (changePcCap: Bool @# ty)
    (newPcCap: Cap @# ty)
    (exception: Bool @# ty)
    (exceptionCause: Data @# ty)
    (exceptionValue: Data @# ty)
    (baseException: Bool @# ty)
    (wbScr: Bool @# ty)
    (scr: FullCapWithTag @# ty)
    (scrException: Bool @# ty)
    (wbCsr: Bool @# ty)
    (csrVal: Data @# ty)
    (scrIdx: ScrId @# ty)
    (csrIdx: Bit CsrIdSz @# ty)
    (exceptionIdx: Bit RegFixedIdSz @# ty): ActionT ty Void :=
    ( Read pcVal : Addr <- @^pcValReg;
      Read pcCap : Cap <- @^pcCapReg;
      LET pcc : FullCapWithTag <- STRUCT { "tag" ::= $$true;
                                           "cap" ::= #pcCap;
                                           "val" ::= #pcVal };
      LETA exceptionPc <- if hasTrap
                          then
                            ( Read mtcc : FullCapWithTag <- @^mtccReg;
                              Ret #mtcc )
                          else Ret #pcc ;

      Write @^pcValReg : Addr <- (IF exception
                                  then #exceptionPc @% "val"
                                  else newPcVal);
      Write @^pcCapReg : Cap <- (IF exception
                                 then #exceptionPc @% "cap"
                                 else ITE changePcCap newPcCap #pcCap);

      Write @^prevPcValReg: Maybe Addr <- STRUCT { "valid" ::= $$true;
                                                   "data" ::= currPcVal };

      if hasTrap
      then
        ( WriteIf mtiReset Then @^mtiReg : Bool <- $$false;
          Read mepccVal : FullCapWithTag <- @^mepccReg;
          Write @^mepccReg : FullCapWithTag <- (IF exception
                                                then #pcc
                                                else (IF scrIdx == $$(getScrId mepcc)
                                                      then scr
                                                      else #mepccVal));

          Read mStatusVal : Data <- @^mStatusReg;
          LET mStatusArr <- unpack (Array Xlen Bool) #mStatusVal;
          LET newMStatusVal <- pack (UpdateArrayConst (UpdateArrayConst #mStatusArr (@natToFin 3 _) ($$false))
                                       (@natToFin 7 _) (#mStatusArr ![3]));
          Write @^mStatusReg : Data <- (IF exception
                                        then #newMStatusVal
                                        else (IF csrIdx == $$(getCsrId mstatus)
                                              then csrVal
                                              else #mStatusVal));

          Read mCauseVal : Data <- @^mCauseReg;
          Write @^mCauseReg : Data <- (IF exception
                                       then ITE baseException exceptionCause $CapException
                                       else (IF wbScr && csrIdx == $$(getCsrId mcause)
                                             then csrVal
                                             else #mCauseVal));
          
          Read mtValVal : Data <- @^mtValReg;
          Write @^mtValReg : Data <- (IF exception
                                      then ITE baseException
                                             exceptionValue
                                             (ZeroExtendTo Xlen
                                                (pack (STRUCT { "S" ::= scrException;
                                                                "capIdx" ::= exceptionIdx;
                                                                "cause" ::= TruncLsbTo RegFixedIdSz _
                                                                              exceptionCause })))
                                      else (IF wbCsr && csrIdx == $$(getCsrId mtval)
                                            then csrVal
                                            else #mtValVal));
          
          
          LETA _ <- writeRegsPred procName scrRegInfos
                      (!exception && (wbScr && scrIdx != $$(getScrId mepcc))) scrIdx scr;

          LETA _ <- writeRegsPred procName csrRegInfos
                      ((!exception && wbCsr) &&
                         (csrIdx != $$(getCsrId mstatus)) &&
                         (csrIdx != $$(getCsrId mcause)) &&
                         (csrIdx != $$(getCsrId mtval)))
                      csrIdx csrVal;

          Retv
        )
      else Retv).

  Definition specTimerIncAndInterruptSetRule :=
    ( if hasTrap
      then
      ( Read mTime : Data <- @^mTimeReg;
        Read mTimeCmp: Data <- @^mTimeCmpReg;
        Read mti: Bool <- @^mtiReg;
        LET msb <- TruncMsbTo 1 (Xlen - 1) (#mTime - #mTimeCmp);
        Write @^mtiReg : Bool <- ITE (isZero #msb) $$true #mti;
        Write @^mTimeReg : Data <- #mTime + $1;
        Retv )
      else Retv ).

  Section ies.
    Variable ies: list InstEntrySpec.

    Section DecExec.
      Variable pcc: FullCap @# ty.
      Variable inst: Inst @# ty.
      Variable cs1 cs2 scr: FullCapWithTag @# ty.
      Variable csr: Data @# ty.

      Definition decExecOutput: FullOutput ## ty :=
        fold_right (fun ie out => (IfE matchUniqId inst (uniqId ie)
                                   then spec ie pcc inst cs1 cs2 scr csr
                                   else out as retOut; RetE #retOut))
          (RetE ((Const ty (getDefaultConst FullOutput))
                   @%[ "exception?" <- $$true ]
                   @%[ "exceptionCause" <- Const ty (natToWord Xlen InstIllegal) ]
                   @%[ "exceptionValue" <- (ZeroExtendTo Xlen inst) ]
                   @%[ "baseException?" <- $$true ])) ies.
    End DecExec.

    Section Index.
      Variable inst: Inst @# ty.
      Variable n: nat.
      Variable idx: Inst @# ty -> Bit n @# ty.
      Variable fn: InstProperties -> word n.

      Definition getIndex: Bit n @# ty :=
        fold_right (fun ie out => (IF matchUniqId inst (uniqId ie)
                                   then (if (weq (fn (instProperties ie)) (wzero n))
                                         then idx inst
                                         else $$(fn (instProperties ie)))
                                   else out))
          ($0) ies.
    End Index.
  
    Definition specDecExecRule :=
      ( Read pcCap : Cap <- @^pcCapReg;
        Read pcVal : Addr <- @^pcValReg;
        Read memArr: Array NumMemBytes FullCapWithTag <- @^memArray;
        LETAE baseTop <- getCapBaseTop (STRUCT { "cap" ::= #pcCap; "val" ::= #pcVal });
        LET topBound <- ZeroExtend 1 #pcVal + $(InstSz/8) <= (#baseTop @% "top");
        LETAE inst <- instReqSpec #memArr #pcVal;
        Read regs : Array NumRegs FullCapWithTag <- @^regsArray;
        LET cs1Idx <- getIndex #inst (@rs1 _) implicitReg;
        LET cs2Idx <- rs2Fixed #inst;
        LET scrIdx <- getIndex #inst (@rs2Fixed _) implicitScr;
        LET csrIdx <- getIndex #inst (@imm _) implicitCsr;
        LET cs1 <- #regs@[#cs1Idx];
        LET cs2 <- #regs@[TruncLsbTo RegIdSz _ #cs2Idx];
        LETA scr <- readRegs procName scrRegInfos #scrIdx FullCapWithTag;
        LETA csr <- readRegs procName csrRegInfos #csrIdx Data;

        LET pcc : FullCap <- STRUCT { "cap" ::= #pcCap;
                                      "val" ::= #pcVal};
        
        LETA mti <- if hasTrap
                    then ( Read mti : Bool <- @^mtiReg;
                           Ret #mti )
                    else Ret $$false;
        LETAE out : FullOutput <-
                      (IfE #mti
                       then RetE ((Const ty (getDefaultConst FullOutput))
                                    @%[ "exception?" <- $$true]
                                    @%[ "exceptionCause" <- {<$$WO~1, $$(natToWord (Xlen-1) TimerInterrupt)>}])
                       else (IfE !#topBound
                             then RetE ((Const ty (getDefaultConst FullOutput))
                                          @%[ "exception?" <- $$true]
                                          @%[ "exceptionCause" <- Const ty (natToWord Xlen CapBoundsViolation)])
                             else decExecOutput #pcc #inst #cs1 #cs2 #scr #csr as out;
                             RetE (Var ty (SyntaxKind FullOutput) out))
                        as out; RetE (Var ty (SyntaxKind FullOutput) out));
        
        LETAE ld <- loadReqSpec #memArr (#out @% "pcMemAddr") (#out @% "memSize") (#out @% "memCap?")
                      (#out @% "ldSigned?");
        LET cd <- ITE (#out @% "mem?" && !(#out @% "store?"))
                    (STRUCT { "tag" ::= #ld @% "tag";
                              "cap" ::= #ld @% "cap";
                              "val" ::= #ld @% "val" } : FullCapWithTag @# ty)
                    (STRUCT { "tag" ::= #out @% "cdTag";
                              "cap" ::= #out @% "cdCap";
                              "val" ::= #out @% "cdVal"} : FullCapWithTag @# ty);
        LET cdIdx <- rd #inst;
        
        LET updRegs <- (#regs @[ #cdIdx <- ITE (!(#out @% "exception?") && (#out @% "wb?") && isNotZero(#cdIdx))
                                             #cd (#regs@[#cdIdx])]);
        Write @^regsArray : Array NumRegs FullCapWithTag <- #updRegs;

        LETAE newMemArr <- storeReqSpec #memArr (!(#out @% "exception?") && (#out @% "mem?") && (#out @% "store?"))
                             (#out @% "pcMemAddr") (#out @% "memSize") (#out @% "memCap?") #cd;
        Write @^memArray : Array NumMemBytes FullCapWithTag <- #newMemArr;

        LETN nativePcVal : _ <- ToNative #pcVal;
        ReadN pcCount : NativeKind (fun (pc: type Addr) => 0) <- @^pcCountNReg;
        WriteN @^pcCountNReg : NativeKind (fun (pc: type Addr) => 0) <-
                                 (Var ty (NativeKind (fun (pc: type Addr) => 0))
                                            (fun (pc: type Addr) => if weqb pc nativePcVal
                                                                    then S (pcCount pc)
                                                                    else pcCount pc));

        handleException
          ((*mtiReset :=*) #mti)
          ((*currPcVal :=*) #pcVal)
          ((*newPcVal :=*) ITE (#out @% "taken?") (#out @% "pcMemAddr") (#pcVal + $(InstSz/8)))
          ((*changePcCap :=*) #out @% "changePcCap?")
          ((*newPcCap :=*) #out @% "pcCap")
          ((*exception :=*) #out @% "exception?")
          ((*exceptionCause :=*) #out @% "exceptionCause")
          ((*exceptionValue :=*) #out @% "exceptionValue")
          ((*baseException :=*) #out @% "baseException?")
          ((*wbScr :=*) #out @% "wbScr?")
          ((*scr :=*) STRUCT { "tag" ::= #out @% "scrTag"; "cap" ::= #out @% "scrCap"; "val" ::= #out @% "scrVal"})
          ((*scrException :=*) #out @% "scrException?")
          ((*wbScr :=*) #out @% "wbScr?")
          ((*csrVal :=*) #out @% "csrVal")
          ((*scrIdx :=*) #scrIdx)
          ((*csrIdx :=*) #csrIdx)
          ((*exceptionIdx :=*) ITE (#out @% "pcCapException?") $0 (ZeroExtendTo RegFixedIdSz #cs1Idx))).
  End ies.
End Run.
