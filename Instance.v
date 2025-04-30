(*
  This script contains the extraction command used to translate the
  RISC-V processor core model into Haskell, which is the first step
  in generating the model's Verilog.
*)

Require Import Kami.All Kami.Compiler.Compiler Kami.Compiler.Rtl Kami.LibMisc.
Require Import ProcKami.FU.
Require Import ProcKami.Pipeline.ProcessorCore.
Require Import ProcKami.MemOps.
Require Import List.
Import ListNotations.
Require Import ProcKami.ModelParams.
Require Import PeanoNat.
Import Nat.
Require Import StdLibKami.RegStruct.
Require Import Kami.Compiler.Test.
Require Import Kami.Simulator.NativeTest.
Require Import Kami.Simulator.CoqSim.Simulator.
Require Import Kami.Simulator.CoqSim.HaskellTypes.
Require Import Kami.Simulator.CoqSim.RegisterFile.
Require Import Kami.Simulator.CoqSim.Eval.
Require Import Kami.WfActionT.
Require Import Kami.SignatureMatch.
Require Import ProcKami.Devices.Uart.

Definition supportedExts
  :  list SupportedExt
  := [
      Build_SupportedExt "I" true true ;
        Build_SupportedExt "M" true true ;
        Build_SupportedExt "A" true true ;
        Build_SupportedExt "F" true true ;
        Build_SupportedExt "D" true true ;
        Build_SupportedExt "C" true true ;
        Build_SupportedExt "S" true true ;
        Build_SupportedExt "U" true true ;
        Build_SupportedExt "Zicsr" true false ;
        Build_SupportedExt "Zifencei" true false
    ].

Definition allow_misaligned      := true.
Definition allow_inst_misaligned := true.
Definition has_misaligned_access_exception     := false.

Definition core (xlens : list nat) : Mod
  := generateCore
       xlens
       supportedExts
       allow_misaligned
       allow_inst_misaligned
       has_misaligned_access_exception
       (_ 'h"1000").

Definition model (xlens : list nat) : Mod
  := generateModel
       xlens
       supportedExts
       allow_misaligned
       allow_inst_misaligned
       has_misaligned_access_exception
       (_ 'h"1000").

Definition modelParams (xlens : list nat) : ProcParams
  := modelProcParams
       xlens
       supportedExts
       allow_misaligned
       allow_inst_misaligned
       has_misaligned_access_exception 
       (_ 'h"1000").

Definition core32 : Mod := core [Xlen32].
Definition core64 : Mod := core [Xlen32; Xlen64].

Definition model32 : Mod := model [Xlen32].
Definition model64 : Mod := model [Xlen32; Xlen64].

Definition model32Params := modelParams [Xlen32].
Definition model64Params := modelParams [Xlen32; Xlen64].

(* verify that the 32 bit model is compatible with TileLink. *)
Goal Nat.log2_up (length (@memOps model32Params)) <= (@TlFullSz model32Params).
Proof. cbv; lia. Qed.

(* verify that the 64 bit model is compatible with TileLink. *)
Goal Nat.log2_up (length (@memOps model64Params)) <= (@TlFullSz model64Params).
Proof. cbv; lia. Qed.

(** vm_compute should take ~40s *)
Lemma model64_wf_unit : WfMod_unit model64 = [].
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma model32_wf_unit : WfMod_unit model32 = [].
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma model64_wf: forall ty, WfMod_new ty model64.
Proof.
  apply WfMod_unit_new.
  apply model64_wf_unit.
Qed.

Lemma model32_wf: forall ty, WfMod_new ty model32.
Proof.
  apply WfMod_unit_new.
  apply model32_wf_unit.
Qed.

Lemma model64_sf : SigMatch_Mod model64 = [].
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma model32_sf : SigMatch_Mod model32 = [].
Proof.
  vm_compute.
  reflexivity.
Qed.

Axiom cheat : forall {X},X.

Definition baseOnly m := let '(_,(_,basemod)) := separateModRemove m in basemod.

Definition basemod32 := baseOnly model32.
Definition basemod64 := baseOnly model64.

Lemma WfCreateHideMod: forall ty ls m, WfMod_new ty (createHideMod m ls) -> WfMod_new ty m.
Proof.
  intros ty.
  induction ls; auto; simpl; intros.
  destruct H; apply IHls; auto.
Qed.

Lemma baseMod_wf: forall ty m, WfMod_new ty m ->
                               WfBaseModule_new ty (baseOnly m).
Proof.
  intros ty m H.
  pose proof (mergeSeparatedRemoved_Wf_new (Build_ModWf_new _ _ H)) as sth.
  simpl in sth.
  apply WfCreateHideMod in sth.
  simpl in sth.
  assert (sth2: WfBaseModule_new ty (snd (snd (separateModRemove m)))) by tauto.
  unfold baseOnly.
  destruct (separateModRemove m) as [x1 x2].
  destruct x2.
  auto.
Qed.

Lemma WfRules_baseMod: forall ty m, WfMod_new ty m -> WfRules ty (getRegisters (baseOnly m)) (getRules (baseOnly m)).
Proof.
  intros ty m H.
  pose proof (baseMod_wf ty m H) as sth.
  destruct sth; auto.
Qed.

Section ListProp.
  Variable A: Type.
  Context [P: A -> Prop].
  Fixpoint conjProp (ls: list A) : Prop :=
    match ls with
    | nil => True
    | x :: xs => P x /\ conjProp xs
    end.

  Fixpoint conjProp_listProp [ls]: conjProp ls -> list { x : A & P x } :=
    match ls return conjProp ls -> list { x : A & P x } with
    | nil => fun _ => nil
    | x :: xs => fun pf => existT P x (proj1 pf) :: conjProp_listProp (proj2 pf)
    end.
End ListProp.

Definition sigTBaseRulesWf ty m (wf: WfMod_new ty m) :=
  conjProp_listProp (WfRules_baseMod ty m wf).

Definition rulesOnly {m} (H: forall ty, WfMod_new ty m): list (evaluated_Rule (getRegisters (baseOnly m))) :=
  map (fun '(existT x pf) => eval_Rule x pf) (sigTBaseRulesWf eval_Kind m (H eval_Kind)).

Definition rules_32 : list (evaluated_Rule (getRegisters basemod32)) := rulesOnly model32_wf.
Definition rules_64 : list (evaluated_Rule (getRegisters basemod64)) := rulesOnly model64_wf.

Set Extraction Output Directory ".".

Separate Extraction
         predPack
         predPackOr
         createWriteRq
         createWriteRqMask
         pointwiseIntersectionNoMask
         pointwiseIntersectionMask
         pointwiseIntersection
         pointwiseBypass
         getDefaultConstFullKind
         CAS_RulesRf
         Fin_to_list

         getCallsWithSignPerMod
         RtlExpr'

         CompActionSimple
         RmeSimple
         RtlModule
         getRules

         separateModRemove
         separateModHidesNoInline

         core32
         core64

         model32
         model64

         rules_32
         rules_64

         testReg
         testAsync
         testSyncIsAddr
         testSyncNotIsAddr
         testNative

         print_Val2
         init_state
         sim_step
         initialize_files_zero

         ZeroExtendTo
         TruncLsbTo
         TruncMsbTo
         .
