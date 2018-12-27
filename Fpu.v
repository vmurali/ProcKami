(*
  This module defines the functional unit entries for floating
  point arithmetic.
*)
Require Import Kami.All.
Require Import FpuKami.Definitions.
Require Import FpuKami.MulAdd.
Require Import FpuKami.Compare.
Require Import Alu.
Require Import FU.
Require Import List.
Import ListNotations.
Require Import RecordUpdate.RecordSet.
Import RecordNotations.

Section Fpu.

Variable Xlen_over_8: nat.
Notation Xlen := (8 * Xlen_over_8)%nat.

Variable ty : Kind -> Type.

Definition exp_width (n : nat) : nat := 3 * n / 32 + 5.

Section exp_width_tests.

Let test_0 : exp_width 32 = 8  := eq_refl 8.
Let test_1 : exp_width 64 = 11 := eq_refl 11.

End exp_width_tests.

Definition sig_width (n : nat) : nat := 29 * n / 32 - 6.

Section sig_width_tests.

Let test_0 : sig_width 32 = 23 := eq_refl 23.
Let test_1 : sig_width 64 = 52 := eq_refl 52.

End sig_width_tests.

Definition sem_in_pkt_kind
  :  Kind
  := MulAdd_Input ((exp_width Xlen) - 2) ((sig_width Xlen) - 2).

Definition sem_out_pkt_kind
  :  Kind
  := MulAdd_Output ((exp_width Xlen) - 2) ((sig_width Xlen) - 2).

Let IEEE_float_kind : Kind
  := FN ((exp_width Xlen) - 2) ((sig_width Xlen) - 2).

Let kami_float_kind : Kind
  := NF ((exp_width Xlen) - 2) ((sig_width Xlen) - 2).

Let fmin_max_in_pkt_kind
  :  Kind
  := STRUCT {
       "arg1" :: kami_float_kind;
       "arg2" :: kami_float_kind;
       "max"  :: Bool
     }.

Let cmp_out_pkt_kind
  :  Kind
  := Compare_Output. (* ((exp_width Xlen) - 2) ((sig_width Xlen) - 2). *)

Local Notation "x [[ proj  :=  v ]]" := (set proj (pure v) x)
                                    (at level 14, left associativity).
Local Notation "x [[ proj  ::=  f ]]" := (set proj f x)
                                     (at level 14, f at next level, left associativity).

Open Scope kami_expr.

Let to_IEEE_float (x : Bit Xlen @# ty)
  :  IEEE_float_kind @# ty
  := unpack IEEE_float_kind (ZeroExtendTruncLsb (size IEEE_float_kind) x).

Let to_kami_float (x : Bit Xlen @# ty)
  :  kami_float_kind @# ty
  := getNF_from_FN (to_IEEE_float x).

Let from_kami_float (x : kami_float_kind @# ty)
  :  Bit Xlen @# ty
  := ZeroExtendTruncLsb Xlen (pack (getFN_from_NF x)).

Let csr_bit (flag : Bool @# ty) (mask : Bit 5 @# ty)
  :  Bit 5 @# ty
  := ITE flag mask ($0 : Bit 5 @# ty).

(*
  Note: this function does not set the divide by zero CSR flag.
*)
Let csr (flags : ExceptionFlags @# ty)
  :  Bit Xlen @# ty
  := ZeroExtendTruncLsb Xlen
     ($0 : Bit 5 @# ty
       | (csr_bit (flags @% "invalid") (Const ty ('b("10000"))))
       | (csr_bit (flags @% "overflow") (Const ty ('b("00100"))))
       | (csr_bit (flags @% "underflow") (Const ty ('b("00010"))))
       | (csr_bit (flags @% "inexact") (Const ty ('b("00001"))))).

Let excs_bit (flag : Bool @# ty) (mask : Bit 4 @# ty)
  :  Exception @# ty
  := ITE flag mask ($0 : Bit 4 @# ty).

Let excs (flags : ExceptionFlags @# ty)
  :  Maybe Exception @# ty
  := STRUCT {
       "valid" ::= flags @% "invalid";
       "data"  ::= excs_bit (flags @% "invalid") ($IllegalInst)
     }.

Let muladd_in_pkt (op : Bit 2 @# ty) (context_pkt_expr : ExecContextPkt Xlen_over_8 ## ty) 
  :  sem_in_pkt_kind ## ty
  := LETE context_pkt
       :  ExecContextPkt Xlen_over_8
       <- context_pkt_expr;
     RetE
       (STRUCT {
         "op" ::= op;
         "a"  ::= to_kami_float (#context_pkt @% "reg1");
         "b"  ::= to_kami_float (#context_pkt @% "reg2");
         "c"  ::= to_kami_float (#context_pkt @% "reg3");
         "roundingMode" ::= rm (#context_pkt @% "inst");
         "detectTininess" ::= $$true
       } : sem_in_pkt_kind @# ty).

Let add_in_pkt (op : Bit 2 @# ty) (context_pkt_expr : ExecContextPkt Xlen_over_8 ## ty) 
  :  sem_in_pkt_kind ## ty
  := LETE context_pkt
       :  ExecContextPkt Xlen_over_8
       <- context_pkt_expr;
     RetE
       (STRUCT {
         "op" ::= op;
         "a"  ::= to_kami_float (#context_pkt @% "reg1");
         "b"  ::= to_kami_float ($0);
         "c"  ::= to_kami_float (#context_pkt @% "reg2");
         "roundingMode" ::= rm (#context_pkt @% "inst");
         "detectTininess" ::= $$true
       } : sem_in_pkt_kind @# ty).

Let mul_in_pkt (op : Bit 2 @# ty) (context_pkt_expr : ExecContextPkt Xlen_over_8 ## ty) 
  :  sem_in_pkt_kind ## ty
  := LETE context_pkt
       :  ExecContextPkt Xlen_over_8
       <- context_pkt_expr;
     RetE
       (STRUCT {
         "op" ::= op;
         "a"  ::= to_kami_float (#context_pkt @% "reg1");
         "b"  ::= to_kami_float (#context_pkt @% "reg2");
         "c"  ::= to_kami_float ($0);
         "roundingMode" ::= rm (#context_pkt @% "inst");
         "detectTininess" ::= $$true
       } : sem_in_pkt_kind @# ty).

Let muladd_out_pkt (sem_out_pkt_expr : sem_out_pkt_kind ## ty)
  :  ExecContextUpdPkt Xlen_over_8 ## ty
  := LETE sem_out_pkt
       :  sem_out_pkt_kind
       <- sem_out_pkt_expr;
     RetE
       (STRUCT {
         "val1" ::= Valid (STRUCT {
                      "tag"  ::= Const ty (natToWord RoutingTagSz FloatRegTag);
                      "data" ::= from_kami_float (#sem_out_pkt @% "out")
                    });
         "val2" ::= Valid (STRUCT {
                      "tag"  ::= Const ty (natToWord RoutingTagSz CsrTag);
                      "data" ::= (csr (#sem_out_pkt @% "exceptionFlags") : Bit Xlen @# ty)
                    });
         "memBitMask" ::= $$(getDefaultConst (Array Xlen_over_8 Bool));
         "taken?" ::= $$false;
         "aq" ::= $$false;
         "rl" ::= $$false;
         "exception" ::= excs (#sem_out_pkt @% "exceptionFlags")
       } : ExecContextUpdPkt Xlen_over_8 @# ty).

Let fmin_max_in_pkt (max : Bool @# ty) (context_pkt_expr : ExecContextPkt Xlen_over_8 ## ty)
  :  fmin_max_in_pkt_kind ## ty
  := LETE context_pkt
       :  ExecContextPkt Xlen_over_8
       <- context_pkt_expr;
     RetE
       (STRUCT {
         "arg1" ::= to_kami_float (#context_pkt @% "reg1");
         "arg2" ::= to_kami_float (#context_pkt @% "reg2");
         "max"  ::= max
       } : fmin_max_in_pkt_kind @# ty).
(*
Let cmp_out_pkt (cmp_out_pkt_expr : cmp_out_pkt_kind ## ty)
  :  ExecContextUpdPkt Xlen_over_8 ## ty
  := LETE cmp_out_pkt
       :  cmp_out_pkt_kind
       <- cmp_out_pkt_expr;
     RetE
       (STRUCT {
         "val1"
           ::= Valid (STRUCT {
                 "tag"  ::= Const ty (natToWord RoutingTagSz FloatRegTag);
                 "data" ::= from_kami_float (#cmp_out_pkt 
               });
       } : ExecContextUpdPkt Xlen_over_8 @# ty).
*)
Definition Mac : @FUEntry Xlen_over_8 ty
  := {|
       fuName :="mac";
       fuFunc := fun sem_in_pkt_expr : sem_in_pkt_kind ## ty
                   => LETE sem_in_pkt
                        :  sem_in_pkt_kind
                        <- sem_in_pkt_expr;
                      MulAdd_expr (#sem_in_pkt);
       fuInsts
         := [
              {|
                instName   := "fmadd.s";
                extensions := ["RV32F"; "RV64F"];
                uniqId
                  := [
                       fieldVal instSizeField ('b"11");
                       fieldVal opcodeField   ('b"10000");
                       fieldVal fmtField      ('b"00")
                     ];
                inputXform  := muladd_in_pkt $0;
                outputXform := muladd_out_pkt;
                optMemXform := None;
                instHints := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrs3 := true]][[hasFrd := true]] 
              |};
              {|
                instName   := "fmsub.s";
                extensions := ["RV32F"; "RV64F"];
                uniqId
                  := [
                       fieldVal instSizeField ('b"11");
                       fieldVal opcodeField   ('b"10001");
                       fieldVal fmtField      ('b"00")
                     ];
                inputXform  := muladd_in_pkt $1;
                outputXform := muladd_out_pkt;
                optMemXform := None;
                instHints := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrs3 := true]][[hasFrd := true]] 
              |};
              {|
                instName   := "fnmsub.s";
                extensions := ["RV32F"; "RV64F"];
                uniqId
                  := [
                       fieldVal instSizeField ('b"11");
                       fieldVal opcodeField   ('b"10010");
                       fieldVal fmtField      ('b"00")
                     ];
                inputXform  := muladd_in_pkt $3;
                outputXform := muladd_out_pkt;
                optMemXform := None;
                instHints := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrs3 := true]][[hasFrd := true]] 
              |};
              {|
                instName   := "fnmadd.s";
                extensions := ["RV32F"; "RV64F"];
                uniqId
                  := [
                       fieldVal instSizeField ('b"11");
                       fieldVal opcodeField   ('b"10011");
                       fieldVal fmtField      ('b"00")
                     ];
                inputXform  := muladd_in_pkt $2;
                outputXform := muladd_out_pkt;
                optMemXform := None;
                instHints := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrs3 := true]][[hasFrd := true]] 
              |};
              {|
                instName   := "fadd.s";
                extensions := ["RV32F"; "RV64F"];
                uniqId
                  := [
                       fieldVal instSizeField ('b"11");
                       fieldVal opcodeField   ('b"10011");
                       fieldVal fmtField      ('b"00");
                       fieldVal funct7Field   ('b"0000000")
                     ];
                inputXform  := add_in_pkt $0;
                outputXform := muladd_out_pkt;
                optMemXform := None;
                instHints := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrd := true]] 
              |};
              {|
                instName   := "fsub.s";
                extensions := ["RV32F"; "RV64F"];
                uniqId
                  := [
                       fieldVal instSizeField ('b"11");
                       fieldVal opcodeField   ('b"10100");
                       fieldVal fmtField      ('b"00");
                       fieldVal funct7Field   ('b"0000100")
                     ];
                inputXform  := add_in_pkt $1;
                outputXform := muladd_out_pkt;
                optMemXform := None;
                instHints := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrd := true]] 
              |};
              {|
                instName   := "fmult.s";
                extensions := ["RV32F"; "RV64F"];
                uniqId
                  := [
                       fieldVal instSizeField ('b"11");
                       fieldVal opcodeField   ('b"10100");
                       fieldVal fmtField      ('b"00");
                       fieldVal funct7Field   ('b"0001000")
                     ];
                inputXform  := mul_in_pkt $0;
                outputXform := muladd_out_pkt;
                optMemXform := None;
                instHints := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrd := true]] 
              |}
            ]
     |}.

Definition FMinMax : @FUEntry Xlen_over_8 ty
  := {|
       fuName := "fmin_max";
       fuFunc
         := fun sem_in_pkt_expr : fmin_max_in_pkt_kind ## ty
              => LETE sem_in_pkt
                   :  fmin_max_in_pkt_kind
                   <- sem_in_pkt_expr;
                 LETE cmp_out_pkt
                   :  cmp_out_pkt_kind
                   <- Compare_expr (#sem_in_pkt @% "arg1") (#sem_in_pkt @% "arg2");
                 LETE result
                   :  Bit Xlen
                   <- RetE
                        (ITE ((#cmp_out_pkt @% "gt") ^^ (#sem_in_pkt @% "max"))
                          (from_kami_float (#sem_in_pkt @% "arg2"))
                          (from_kami_float (#sem_in_pkt @% "arg1")));
                 RetE
                   (STRUCT {
                     "val1"
                       ::= Valid (STRUCT {
                             "tag"  ::= $$(natToWord RoutingTagSz FloatRegTag);
                             "data" ::= #result
                           });
                     "val2" ::= @Invalid ty _;
                     "memBitMask" ::= $$(getDefaultConst (Array Xlen_over_8 Bool));
                     "taken?" ::= $$false;
                     "aq" ::= $$false;
                     "rl" ::= $$false;
                     "exception" ::= @Invalid ty _
                   } : ExecContextUpdPkt Xlen_over_8 @# ty);
       fuInsts
         := [
              {|
                instName   := "fmin.s";
                extensions := ["RV32F"; "RV64F"];
                uniqId
                  := [
                       fieldVal instSizeField ('b"11");
                       fieldVal opcodeField   ('b"10100");
                       fieldVal funct3Field   ('b"000");
                       fieldVal funct7Field   ('b"0010100")
                     ];
                inputXform := fmin_max_in_pkt ($$false);
                outputXform := fun fmin_max_pkt_expr => fmin_max_pkt_expr;
                optMemXform := None;
                instHints := falseHints[[hasFrs1 := true]][[hasFrs2 := true]][[hasFrd := true]] 
              |}
            ]
     |}.

Close Scope kami_expr.

End Fpu.