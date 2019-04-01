(*
  This module defines the functional unit entries for floating
  point arithmetic.

  TODO: WARNING: check that the instructions set exceptions on invalid rounding modes.
*)
Require Import Vector.
Import VectorNotations.
Require Import Kami.All.
Require Import FpuKami.Definitions.
Require Import FpuKami.MulAdd.
Require Import FpuKami.Compare.
Require Import FpuKami.NFToIN.
Require Import FpuKami.INToNF.
Require Import FpuKami.Classify.
Require Import FpuKami.ModDivSqrt.
Require Import FU.
Require Import List.
Import ListNotations.

Section Fpu.

  Variable Xlen_over_8: nat.
  Variable Rlen_over_8: nat. (* the "result" length, specifies the size of values stored in the context and update packets. *)

  Variable fu_params : fu_params_type.
  Variable ty : Kind -> Type.

  Local Notation Rlen := (8 * Rlen_over_8).
  Local Notation Xlen := (8 * Xlen_over_8).
  Local Notation PktWithException := (PktWithException Xlen_over_8).
  Local Notation ExecContextUpdPkt := (ExecContextUpdPkt Rlen_over_8).
  Local Notation ExecContextPkt := (ExecContextPkt Xlen_over_8 Rlen_over_8).
  Local Notation FullException := (FullException Xlen_over_8).
  Local Notation FUEntry := (FUEntry Xlen_over_8 Rlen_over_8).
  Local Notation RoutedReg := (RoutedReg Rlen_over_8).
  Local Notation NFToINOutput := (NFToINOutput (Xlen - 2)).
  Local Notation INToNFInput := (INToNFInput (Xlen - 2)).

  Local Notation expWidthMinus2 := (fu_params_expWidthMinus2 fu_params).
  Local Notation sigWidthMinus2 := (fu_params_sigWidthMinus2 fu_params).
  Local Notation exp_valid      := (fu_params_exp_valid fu_params).
  Local Notation sig_valid      := (fu_params_sig_valid fu_params).
  Local Notation suffix         := (fu_params_suffix fu_params).
  Local Notation int_suffix     := (fu_params_int_suffix fu_params).
  Local Notation format_field   := (fu_params_format_field fu_params).
  Local Notation exts           := (fu_params_exts fu_params).
  Local Notation exts_32        := (fu_params_exts_32 fu_params).
  Local Notation exts_64        := (fu_params_exts_64 fu_params).

  Local Notation len := ((expWidthMinus2 + 1 + 1) + (sigWidthMinus2 + 1 + 1))%nat.

  Definition bitToFN (x : Bit len @# ty)
    :  FN expWidthMinus2 sigWidthMinus2 @# ty
    := unpack (FN expWidthMinus2 sigWidthMinus2) (ZeroExtendTruncLsb (size (FN expWidthMinus2 sigWidthMinus2)) x).

  Definition bitToNF (x : Bit len @# ty)
    :  NF expWidthMinus2 sigWidthMinus2 @# ty
    := getNF_from_FN (bitToFN x).

  Definition NFToBit (x : NF expWidthMinus2 sigWidthMinus2 @# ty)
    :  Bit len @# ty
    := ZeroExtendTruncLsb len (pack (getFN_from_NF x)).

  Open Scope kami_expr.

  Definition csr (flags : ExceptionFlags @# ty)
    :  Bit Rlen @# ty
    := ZeroExtendTruncLsb Rlen (pack flags).

  Definition rounding_mode_kind : Kind := Bit 3.

  Definition rounding_mode_dynamic : rounding_mode_kind @# ty := Const ty ('b"111").

  Definition rounding_mode (context_pkt : ExecContextPkt @# ty)
    :  rounding_mode_kind @# ty
    := let rounding_mode
         :  rounding_mode_kind @# ty
         := rm (context_pkt @% "inst") in
       ITE
         (rounding_mode == rounding_mode_dynamic)
         (fcsr_frm (context_pkt @% "fcsr"))
         rounding_mode.

  Definition FDivSqrtInput (sqrt : Bool @# ty) (context_pkt_expr : ExecContextPkt ## ty)
    :  inpK expWidthMinus2 sigWidthMinus2 ## ty
    := LETE context_pkt
         :  ExecContextPkt
         <- context_pkt_expr;
       RetE
         (STRUCT {
            "isSqrt" ::= sqrt;
            "nfA"    ::= bitToNF (ZeroExtendTruncLsb len (#context_pkt @% "reg1"));
            "nfB"    ::= bitToNF (ZeroExtendTruncLsb len (#context_pkt @% "reg2"));
            "round"  ::= rounding_mode (#context_pkt);
            "tiny"   ::= $$true
          } : inpK expWidthMinus2 sigWidthMinus2 @# ty).

  Definition FDivSqrtOutput (sem_out_pkt_expr : outK expWidthMinus2 sigWidthMinus2 ## ty)
    :  PktWithException ExecContextUpdPkt ## ty
    := LETE sem_out_pkt
         :  outK expWidthMinus2 sigWidthMinus2
         <- sem_out_pkt_expr;
       SystemE [
         DispString ty "fdivsqrt outK: ";
         DispStruct #sem_out_pkt
           (Vector.nth [
              (1, Binary);   (* isSqrt *)
              (100, Binary); (* inNf *)
              (100, Binary); (* outNf *)
              (10, Binary);  (* outNFException *)
              (10, Binary);  (* exception *)
              (1, Binary);   (* invalidExc *)
              (1, Binary)    (* infiniteExc *)
            ]%vector);
         DispString ty "\n"
       ];
       RetE
         (STRUCT {
            "fst"
              ::= (STRUCT {
                     "val1"
                       ::= Valid (STRUCT {
                             "tag" ::= Const ty (natToWord RoutingTagSz FloatRegTag);
                             "data"
                               ::= (ZeroExtendTruncLsb Rlen
                                      (pack (NFToBit (#sem_out_pkt @% "outNf")))
                                    : Bit Rlen @# ty)
                           });
                     "val2"
                       ::= Valid (STRUCT {
                             "tag"  ::= Const ty (natToWord RoutingTagSz FloatCsrTag);
                             "data" ::= (csr (#sem_out_pkt @% "exception") : Bit Rlen @# ty)
                           });
                     "memBitMask" ::= $$(getDefaultConst (Array Rlen_over_8 Bool));
                     "taken?" ::= $$false;
                     "aq" ::= $$false;
                     "rl" ::= $$false
                   } : ExecContextUpdPkt @# ty);
            "snd" ::= Invalid
          } : PktWithException ExecContextUpdPkt @# ty).

  Definition FDivSqrt
    :  @FUEntry ty
    := {|
         fuName := append "fdivsqrt" suffix;
         fuFunc
           := fun sem_in_pkt_expr : inpK expWidthMinus2 sigWidthMinus2 ## ty
                => LETE sem_in_pkt
                     :  inpK expWidthMinus2 sigWidthMinus2
                     <- sem_in_pkt_expr;
                   div_sqrt_expr (#sem_in_pkt);
         fuInsts
           := [
                {|
                  instName   := append "fdiv" suffix;
                  extensions := exts;
                  uniqId
                    := [
                         fieldVal fmtField format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal rs3Field      ('b"00011")
                       ];
                  inputXform  := FDivSqrtInput ($$false);
                  outputXform := FDivSqrtOutput;
                  optMemXform := None;
                  instHints   := falseHints{*hasFrs1 := true*}{*hasFrs2 := true*}{*hasFrd := true*}
                |};
                {|
                  instName   := append "fsqrt" suffix;
                  extensions := exts;
                  uniqId
                    := [
                         fieldVal fmtField format_field;
                         fieldVal instSizeField ('b"11");
                         fieldVal opcodeField   ('b"10100");
                         fieldVal rs2Field      ('b"00000");
                         fieldVal rs3Field      ('b"01011")
                       ];
                  inputXform  := FDivSqrtInput ($$true);
                  outputXform := FDivSqrtOutput;
                  optMemXform := None;
                  instHints   := falseHints{*hasFrs1 := true*}{*hasFrd := true*}
                |}
              ]
       |}.

  Close Scope kami_expr.

End Fpu.