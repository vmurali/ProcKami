Require Import Kami.AllNotations ProcKami.CheriTypes.
Require Import List.

Theorem negNegPlus n (a b: Bit n @# type): (evalExpr (a + b) = evalExpr (a - ($0 - b)))%kami_expr.
Proof.
  simpl.
  unfold natToWord; simpl.
  rewrite ?wminus_def, ?wzero_wplus.
  rewrite wneg_idempotent.
  auto.
Qed.
  
Definition OneHotKor ty k (ls: list ((Bool @# ty) * (k @# ty))) :=
  Kor (map (fun x => ITE (fst x) (snd x) (Const _ Default)) ls).

Definition SignOrZeroExt ty m (sign: Bool @# ty) n (e: Bit n @# ty) :=
  ITE sign (SignExtend m e) (ZeroExtend m e).

Definition SignOrZeroExtUnsafe ty m (sign: Bool @# ty) n (e: Bit n @# ty) :=
  ITE sign (SignExtendTruncLsb m e) (ZeroExtendTruncLsb m e).

Definition Trunc32 ty m (sign: Bool @# ty) n (e: Bit n @# ty) :=
  SignOrZeroExtUnsafe m sign (ZeroExtendTruncLsb 32 e).

Section FuncUnit.
  Variable procParams: ProcParams.
  Variable ty: Kind -> Type.
  Local Open Scope kami_expr.

  Variable pcc: FullCap @# ty.
  Variable inst: Inst @# ty.
  Variable cs1: FullCapWithTag @# ty.
  Variable cs2: FullCapWithTag @# ty.
  Variable ie: Bool @# ty.

  Variable signExtend: Bool @# ty.
  
  Variable addIn1Cs addIn1Pc addIn10: Bool @# ty.
  Variable addIn2Cs addIn2Imm addIn2Aui: Bool @# ty.

  Variable addNegIn1Cs addNegIn1Pc addNegIn1Add: Bool @# ty.
  Variable addNegIn2Cs addNegIn20 addNegIn2Base: Bool @# ty.
  Variable addNegConst: Addr @# ty.
  Variable addNegSlt: Bool @# ty.

  Variable andIn1Cs andIn1Perms andIn1AddNeg: Bool @# ty.
  Variable andIn2Cs andIn2Imm andIn2Lsh: Bool @# ty.
  Variable andIsOr: Bool @# ty.

  Variable restIn2Imm: Bool @# ty.

  Variable lshIn1Cs: Bool @# ty.
  Variable lshIn2Cs lshIn2Imm lshIn2Exp: Bool @# ty.

  Variable capBoundsJustLen: Bool @# ty.

  Variable truncW: Bool @# ty.

  Variable addDo andDo xorDo rshDo lshDo: Bool @# ty.

  Variable topBoundsSz: Bit (Nat.log2_up (S ((Xlen + CapSz)/8))) @# ty.

  Definition baseFuncUnit :=
    ( LETC cs1Val_SXlen <- SignOrZeroExt 1 signExtend (cs1 @% "val");
      LETC cs2Val_SXlen <- SignOrZeroExt 1 signExtend (cs2 @% "val");
      LETC imm_Xlen <- SignOrZeroExtUnsafe Xlen signExtend (imm inst);
      LETC imm_SXlen <- SignOrZeroExt 1 signExtend #imm_Xlen;
      LETC pc_SXlen <- SignOrZeroExt 1 signExtend (pcc @% "val");

      LETC auiLui <- auiLuiOffset inst;
      LETC aui_SXlen <- SignExtendTruncLsb (Xlen + 1) #auiLui;

      LETC addIn1 <- OneHotKor [(addIn1Cs, #cs1Val_SXlen);
                                (addIn1Pc, #pc_SXlen);
                                (addIn10, $0)];
      LETC addIn2 <- OneHotKor [(addIn2Cs, #cs2Val_SXlen);
                                (addIn2Imm, #imm_SXlen);
                                (addIn2Aui, #aui_SXlen)];
      LETC add_SXlen <- #addIn1 + #addIn2;
      LETC addMsb <- UniBit (TruncMsb Xlen 1) #add_SXlen;
      LETC add <- UniBit (TruncLsb Xlen 1) #add_SXlen;

      LETC addNegIn1 <- OneHotKor [(addNegIn1Cs, #cs1Val_SXlen);
                                   (addNegIn1Pc, #pc_SXlen);
                                   (addNegIn1Add, #add_SXlen)];
      LETC addNegIn2 <- OneHotKor [(addNegIn2Cs, #cs2Val_SXlen);
                                   (addNegIn20, $0)];
                                   
      LETC in1_Xlen <- cs1 @% "val";
      LETC in2_Xlen <- ITE restIn2Imm #imm_Xlen (cs1 @% "val");
      LETC xor <- #in1_Xlen .^ #in2_Xlen;

      LETC rshIn1_SXlen <- ITE truncW (Trunc32 (Xlen + 1) signExtend (cs1 @% "val")) #cs1Val_SXlen;
      LETC rsh <- #rshIn1_SXlen >>> (ZeroExtendTruncLsb (Nat.log2_up Xlen) #in2_Xlen);

      LETC capBoundsIn1 <- ITE capBoundsJustLen $0 (cs1 @% "val");
      LETC capBoundsIn2 <- ITE capBoundsJustLen (cs1 @% "val") (cs2 @% "val");
      LETE capBounds <- getCapBounds capAccessors #capBoundsIn1 #capBoundsIn2;

      LETC lshIn1 <- ITE lshIn1Cs (cs1 @% "val") ($$(wones Xlen));
      LETC lshIn2 <- OneHotKor [(lshIn2Cs, ZeroExtendTruncLsb (Nat.log2_up Xlen) (cs2 @% "val"));
                                (lshIn2Imm, ZeroExtendTruncLsb (Nat.log2_up Xlen) #imm_Xlen);
                                (lshIn2Exp, #capBounds @% "exp")];
      LETC lsh <- #lshIn1 << #lshIn2;

      LETE perms1 <- getCapPerms capAccessors (cs1 @% "cap");
      LETE perms2 <- getCapPerms capAccessors (cs2 @% "cap");
      
      LETC andIn1 <- OneHotKor [(andIn1Cs, cs1 @% "val");
                                (andIn1Perms, ZeroExtendTruncLsb Xlen (pack #perms1));
                                (andIn1AddNeg, #add)]; (* TODO: Must change to #subRes most likely *)
      LETC andIn2 <- OneHotKor [(andIn2Cs, cs2 @% "val");
                                (andIn2Imm, #imm_Xlen);
                                (andIn2Lsh, #lsh)];

      LETC andRes <- (ITE andIsOr (~#andIn1) #andIn1) .& (ITE andIsOr (~#andIn2) #andIn2);
      LETC and <- ITE andIsOr (~#andRes) #andRes;

      LETC lui <- SignExtendTruncLsb Xlen ({< #auiLui, $$(wzero 12) >});

      LETE baseTop1 <- getCapBaseTop capAccessors (cs1 @% "cap") (cs1 @% "val");
      LETC base1 <- #baseTop1 @% "base";
      LETC top1 <- #baseTop1 @% "top";
      LETE baseTop2 <- getCapBaseTop capAccessors (cs2 @% "cap") (cs2 @% "val");
      LETC base2 <- #baseTop2 @% "base";
      LETC top2 <- #baseTop2 @% "top";

      (*
      LETC inBoundsCheckAddr <- OneHotKor [(inBoundsAdd, #addRes);
                                           (inBoundsSet, cs2 @% "val")];
       *)

(*       LETC add <- ITE addSlt (ZeroExtendTruncLsb Xlen (pack #addMsb)) #addRes; *)
      RetE $$false
    ).
End FuncUnit.
