Require Import Kami.AllNotations.
Require Import ProcKami.Cheriot.Types ProcKami.Cheriot.BankedMem ProcKami.Cheriot.DecExec ProcKami.Cheriot.CsrScr.

Section Run.
  Context `{procParams: ProcParams}.
  Variable ty: Kind -> Type.
  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Variable uncompressFn: CompInst @# ty -> Maybe Inst ## ty.
  Variable funcEntries: list FuncEntry.

  Definition FetchOut := STRUCT_TYPE {
                             "pc" :: FullCap;
                             "inst" :: Inst;
                             "bounds?" :: Bool }.

  Definition fetch: ActionT ty FetchOut :=
    ( Read pcCap : Cap <- pcCapReg;
      Read pcVal : Addr <- pcValReg;
      LETA rawInst <- instReq #pcVal;
      LET notCompressed <- isInstNotCompressed #rawInst;
      LETAE baseTop <- getCapBaseTop capAccessors #pcCap #pcVal;
      LET baseBound <- #pcVal >= (#baseTop @% "base");
      LET topBound <- ZeroExtend 1 #pcVal + (ITE #notCompressed $4 $2) <= (#baseTop @% "top");
      Ret ((STRUCT { "pc" ::= STRUCT { "cap" ::= #pcCap ; "val" ::= #pcVal } ;
                     "inst" ::= #rawInst;
                     "bounds?" ::= #baseBound && #topBound }): FetchOut @# ty )).

  Definition UncompressOut := STRUCT_TYPE {
                                  "pc" :: FullCap;
                                  "inst" :: Inst;
                                  "bounds?" :: Bool;
                                  "legal?" :: Bool }.

  Definition uncompressValid (fetchOut: FetchOut @# ty) : ActionT ty UncompressOut :=
    ( LET notCompressed <- isInstNotCompressed (fetchOut @% "inst");      
      LETAE maybeUncompressedInst <- uncompressFn (ZeroExtendTruncLsb CompInstSz (fetchOut @% "inst"));
      Ret ((STRUCT { "pc" ::= fetchOut @% "pc";
                     "inst" ::= ITE #notCompressed (fetchOut @% "inst") (#maybeUncompressedInst @% "data");
                     "bounds?" ::= fetchOut @% "bounds?";
                     "legal?" ::= #maybeUncompressedInst @% "valid" }) : UncompressOut @# ty)).

  Definition uncompressInvalid (fetchOut: FetchOut @# ty) : ActionT ty UncompressOut :=
    ( LET notCompressed <- isInstNotCompressed (fetchOut @% "inst");
      Ret ((STRUCT { "pc" ::= fetchOut @% "pc";
                     "inst" ::= fetchOut @% "inst";
                     "bounds?" ::= fetchOut @% "bounds?";
                     "legal?" ::= #notCompressed }) : UncompressOut @# ty)).

  Definition uncompress (fetchOut: FetchOut @# ty): ActionT ty UncompressOut :=
    if compressed
    then uncompressValid fetchOut
    else uncompressInvalid fetchOut.

  Definition regsFile :=
    {|rfIsWrMask := false;
      rfNum := 1;
      rfDataArray := regsArray;
      rfRead := Async [regsRead1; regsRead2];
      rfWrite := regsWrite;
      rfIdxNum := Nat.pow 2 RegIdSz;
      rfData := FullCapWithTag;
      rfInit := regsInit |}.
  
  Definition regReadDecodeOut (uncompressOut: UncompressOut @# ty) :=
    ( LET inst <- uncompressOut @% "inst";
      LETAE allMatches <- matchFuncEntry #inst funcEntries;
      LET hasCs1Prop <- propertiesFuncEntry #allMatches hasCs1;
      LET hasCs2Prop <- propertiesFuncEntry #allMatches hasCs2;
      LET hasScrProp <- propertiesFuncEntry #allMatches hasScr;
      LET hasCsrProp <- propertiesFuncEntry #allMatches hasCsr;
      LET implicitReadProp <- propertiesFuncEntry #allMatches (fun p => Nat.eqb (implicit p) ImplicitRead);
      LET implicitMepccProp <- propertiesFuncEntry #allMatches implicitMepcc;
      LET implicitIeProp <- propertiesFuncEntry #allMatches implicitIe;

      LET getCs1Idx <- ITE #implicitReadProp $ImplicitRead (rs1 #inst);
      LET getCs2Idx <- rs2 #inst;
      LET getScrIdx <- ITE #implicitMepccProp $MepccAddr (rs2Fixed #inst);
      LET getCsrIdx <- ITE #implicitIeProp $$MStatusAddr (imm #inst);

      LETA cs1 <- ( If !(#hasCs1Prop || #implicitReadProp)
                    then ( Nondet rand: FullCapWithTag;
                           Ret #rand )
                    else ( If #getCs1Idx == $0
                           then Ret (Const ty Default)
                           else callReadRegFile FullCapWithTag regsRead1 #getCs1Idx as retVal;
                           Ret #retVal ) as ret;
                    Ret #ret);

      LETA cs2 <- ( If !#hasCs2Prop
                    then ( Nondet rand: FullCapWithTag;
                           Ret #rand )
                    else ( If #getCs2Idx == $0
                           then Ret (Const ty Default)
                           else callReadRegFile FullCapWithTag regsRead2 #getCs2Idx as retVal;
                           Ret #retVal ) as ret;
                    Ret #ret);

      LETA scr <- ( If !(#hasScrProp || #implicitMepccProp)
                    then ( Nondet rand: FullCapWithTag;
                           Ret #rand)
                    else ( readRegs scrs FullCapWithTag #getScrIdx ) as retVal;
                    Ret #retVal );

      LETA csr <- ( If !(#hasCsrProp || #implicitIeProp)
                    then ( Nondet rand: Data;
                           Ret #rand)
                    else ( readRegs csrs Data #getCsrIdx ) as retVal;
                    Ret #retVal );
      Retv ).
End Run.


(* TODOs:
- Fetch: Implicitly reads pc, returns (inBounds, inst)
- Uncompress: Takes in inst, returns (validCompressed || uncompressed, inst)
- RegRead: Takes in inst post compression, implicitly reads relevant registers return (cs1, cs2, scr, csr, ie)
- Decode: Takes in (pc, inst post compression, cs1, cs2, scr, csr, ie), returns the decode output
- Execute: Takes in decode output, returns FuncOutput
- Exception: Consolidates exceptions from Fetch, Uncompress, Decode, Execute, returns FuncOutput with exceptions
- Mem: Takes MemInfo from FuncOutput with exceptions, implicitly performs memory ops, returns FuncOutput with memory updates
- Wb: Takes FuncOutput with memory updates, implicitly writes to PC and registers.
*)
