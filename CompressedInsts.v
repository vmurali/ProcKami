(*
  This file defines the Compressed Instructions Table. This table
  records all of the compressed RISC-V instructions and the bit
  string transformations needed to convert them into their equivalent
  uncompressed RISC-V instructions.
 *)
Require Import Kami.All.
Import Syntax.
Require Import FU.
Require Import List.
Import ListNotations.

Section database.

  Open Scope kami_expr.

  Variable ty : Kind -> Type.

  Definition comp_inst_width : nat := 16.

  Definition uncomp_inst_width : nat := 32.

  Definition comp_inst_kind : Kind := Bit comp_inst_width.

  Definition uncomp_inst_kind : Kind := Bit uncomp_inst_width.

  Record CompInst := {
    req_exts: list (list string);
    comp_inst_id: UniqId;
    decompress: comp_inst_kind @# ty -> uncomp_inst_kind ## ty
                  }.


  (* common compressed instruction field ranges. *)
  Definition comp_inst_opcode_field := (1, 0).
  Definition comp_inst_funct3_field := (15, 13).

  (* compressed register instruction field ranges. *)
  Definition comp_inst_cr_rs2_field := (6, 2).
  Definition comp_inst_cr_rs1_field := (7, 11).
  Definition comp_inst_cr_funct4_field := (15, 12).

  (* compressed store stack instruction field ranges. *)
  Definition comp_inst_css_rs2_field := (6, 2).
  Definition comp_inst_css_imm_field := (7, 12).

  (* compressed wide immediate instruction field ranges. *)
  Definition comp_inst_ciw_rd_field  := (4, 2).
  Definition comp_inst_ciw_imm_field := (12, 5).

  (* compressed load instruction field ranges. *)
  Definition comp_inst_cl_rd_field := (4, 2).
  Definition comp_inst_cl_rs_field := (9, 7).

  (* compressed store instruction field ranges. *)
  Definition comp_inst_cs_rs2_field := (4, 2).
  Definition comp_inst_cs_rs1_field := (9, 7).

  (* compressed arithmetic instruction field ranges. *)
  Definition comp_inst_ca_rs2_field := (4, 2).
  Definition comp_inst_ca_rs1_field := (9, 7). (* also rd *)
  Definition comp_inst_ca_funct6_field := (15, 10).

  (* compressed branch instruction field ranges. *)
  Definition comp_inst_cb_rs1_field := (9, 7).

  (* compressed jump instruction field ranges. *)
  Definition comp_inst_cj_target_field := (12, 2).

  (* TODO: verify *)
  Definition uncomp_inst_reg (xn : nat) : Bit 5 @# ty := $(xn).

  Definition comp_inst_map_reg
             (comp_inst_reg : Bit 3 @# ty)
    :  Bit 5 @# ty
    := Switch comp_inst_reg Retn Bit 5 With {
                ($$(('b"000") : word 3)) ::= uncomp_inst_reg 8;
                ($$(('b"001") : word 3)) ::= uncomp_inst_reg 9;
                ($$(('b"010") : word 3)) ::= uncomp_inst_reg 10;
                ($$(('b"011") : word 3)) ::= uncomp_inst_reg 11;
                ($$(('b"100") : word 3)) ::= uncomp_inst_reg 12;
                ($$(('b"101") : word 3)) ::= uncomp_inst_reg 13;
                ($$(('b"110") : word 3)) ::= uncomp_inst_reg 14;
                ($$(('b"111") : word 3)) ::= uncomp_inst_reg 15
              }.

  Let extensions_all := [["RV32C"]; ["RV64C"]].

  (*
  pg 106 for compressed instructions (122)
  pg 148 for uncompressed instruction (164)

  TODO: verify immediate values - are these multiplied by 4, 8, etc?
   *)
  Definition comp_inst_db
    :  list CompInst
    := [
        (* C.ADDI4SPN  => ADDI checked *)
        Build_CompInst
          extensions_all
          ([
              fieldVal comp_inst_opcode_field ('b"00");
                fieldVal comp_inst_funct3_field ('b"000")
          ])
          (fun comp_inst
           => RetE (
                  {<
                   (ZeroExtend 4 ({<
                                   (comp_inst $[10:7]),
                                   (comp_inst $[12:11]),
                                   (comp_inst $[5:5]),
                                   (comp_inst $[6:6])
                                   >})),
                   uncomp_inst_reg 2,
                   $$(('b"000") : word 3),
                   comp_inst_map_reg (comp_inst $[4:2]),
                   $$(('b"0010011") : word 7)
                   >}
          ));
          (* C.FLD => FLD checked *)
          Build_CompInst
            [["RV32D"; "RV32C"];
               ["RV64D"; "RV64C"]]
            ([
                fieldVal comp_inst_opcode_field ('b"00");
                  fieldVal comp_inst_funct3_field ('b"001")
            ])
            (fun comp_inst
             => RetE (
                    {<
                     (ZeroExtend 7 ({< (comp_inst $[6:5]), (comp_inst $[12:10]) >})),
                     comp_inst_map_reg (comp_inst $[9:7]),
                     $$(('b"011") : word 3),
                     comp_inst_map_reg (comp_inst $[4:2]),
                     $$(('b"0000111") : word 7)
                     >}
            ));
          (* C.LW => LW checked *)
          Build_CompInst
            extensions_all
            ([
                fieldVal comp_inst_opcode_field ('b"00");
                  fieldVal comp_inst_funct3_field ('b"010")
            ])
            (fun comp_inst
             => RetE (
                    {<
                     (ZeroExtend 7 ({< (comp_inst $[5:5]), (comp_inst $[12:10]), (comp_inst $[6:6]) >})),
                     comp_inst_map_reg (comp_inst $[9:7]),
                     $$(('b"010") : word 3),
                     comp_inst_map_reg (comp_inst $[4:2]),
                     $$(('b"0000011") : word 7)
                     >}
            ));
          (* C.FLW => FLW checked *)
          Build_CompInst
            [["RV32F"; "RV32C"]]
            ([
                fieldVal comp_inst_opcode_field ('b"00");
                  fieldVal comp_inst_funct3_field ('b"011")
            ])
            (fun comp_inst
             => RetE (
                    {<
                     (ZeroExtend 7 ({< (comp_inst $[5:5]), (comp_inst $[12:10]), (comp_inst $[6:6]) >})),
                     comp_inst_map_reg (comp_inst $[9:7]),
                     $$(('b"010") : word 3),
                     comp_inst_map_reg (comp_inst $[4:2]),
                     $$(('b"0000111") : word 7)
                     >}
            ));
          (* C.LD => LD checked *)
          Build_CompInst
            [["RV64C"]]
            ([
                fieldVal comp_inst_opcode_field ('b"00");
                  fieldVal comp_inst_funct3_field ('b"011")
            ])
            (fun comp_inst
             => RetE (
                    {<
                     (ZeroExtend 7 ({< (comp_inst $[6:5]), (comp_inst $[12:10]) >})),
                     comp_inst_map_reg (comp_inst $[9:7]),
                     $$(('b"011") : word 3),
                     comp_inst_map_reg (comp_inst $[4:2]),
                     $$(('b"0000011") : word 7)
                     >}
            ));
          (* C.FSD => FSD checked *)
          Build_CompInst
            [
              ["RV32D"; "RV32C"];
                ["RV64D"; "RV64C"]
            ]
            ([
                fieldVal comp_inst_opcode_field ('b"00");
                  fieldVal comp_inst_funct3_field ('b"101")
            ])
            (fun comp_inst
             => let imm
                    := (ZeroExtend 7 ({< (comp_inst $[6:5]), (comp_inst $[12:10]) >})) in
                RetE (
                    {<
                     (imm $[11:5]),
                     comp_inst_map_reg (comp_inst $[4:2]),
                     comp_inst_map_reg (comp_inst $[9:7]),
                     $$(('b"011") : word 3),
                     (imm $[4:0]),
                     $$(('b"0100111") : word 7)
                     >}
            ));
          (* C.SW => SW checked *)
          Build_CompInst
            extensions_all
            ([
                fieldVal comp_inst_opcode_field ('b"00");
                  fieldVal comp_inst_funct3_field ('b"110")
            ])
            (fun comp_inst
             => let imm
                    := (ZeroExtend 7 ({< (comp_inst $[5:5]), (comp_inst $[12:10]), (comp_inst $[6:6]) >})) in
                RetE (
                    {<
                     (imm $[11:5]),
                     comp_inst_map_reg (comp_inst $[4:2]),
                     comp_inst_map_reg (comp_inst $[9:7]),
                     $$(('b"010") : word 3),
                     (imm $[4:0]),
                     $$(('b"0100011") : word 7)
                     >}
            ));
          (* C.FSW => FSW checked *)
          Build_CompInst
            [["RV32F"; "RV32C"]]
            ([
                fieldVal comp_inst_opcode_field ('b"00");
                  fieldVal comp_inst_funct3_field ('b"111")
            ])
            (fun comp_inst
             => let imm
                    := (ZeroExtend 7 ({< (comp_inst $[5:5]), (comp_inst $[12:10]), (comp_inst $[6:6]) >})) in
                RetE (
                    {<
                     (imm $[11:5]),
                     comp_inst_map_reg (comp_inst $[4:2]),
                     comp_inst_map_reg (comp_inst $[9:7]),
                     $$(('b"010") : word 3),
                     (imm $[4:0]),
                     $$(('b"0100111") : word 7)
                     >}
            ));
          (* C.SD => SD checked *)
          Build_CompInst
            [["RV64C"]]
            ([
                fieldVal comp_inst_opcode_field ('b"00");
                  fieldVal comp_inst_funct3_field ('b"111")
            ])
            (fun comp_inst
             => let imm
                    := (ZeroExtend 7 ({< (comp_inst $[6:5]), (comp_inst $[12:10]) >})) in
                RetE (
                    {<
                     (imm $[11:5]),
                     comp_inst_map_reg (comp_inst $[4:2]),
                     comp_inst_map_reg (comp_inst $[9:7]),
                     $$(('b"011") : word 3),
                     (imm $[4:0]),
                     $$(('b"0100011") : word 7)
                     >}
            ));
          (* 
      C.ADDI and C.NOP checked
      C.ADDI => ADDI checked
      C.NOP => NOP = ADDI
           *)
          Build_CompInst
            extensions_all
            ([
                fieldVal comp_inst_opcode_field ('b"01");
                  fieldVal comp_inst_funct3_field ('b"000")
            ])
            (fun comp_inst : Bit 16 @# ty
             => let rd : Bit 5 @# ty := comp_inst $[11:7] in
                RetE (
                    {<
                     (ZeroExtend 6 ({< (comp_inst $[12:12]), (comp_inst $[6:2]) >})),
                     rd,
                     $$(('b"000") : word 3),
                     rd,
                     $$(('b"0010011") : word 7)
                     >}
            ));
          (* C.JAL => JAL checked *)
          Build_CompInst
            [["RV32C"]]
            ([
                fieldVal comp_inst_opcode_field ('b"01");
                  fieldVal comp_inst_funct3_field ('b"001")
            ])
            (fun comp_inst
             => let imm
                    : Bit 20 @# ty
                    := ZeroExtend 9 ({<
                                      (comp_inst $[12:12]),
                                      (comp_inst $[8:8]),
                                      (comp_inst $[10:9]),
                                      (comp_inst $[6:6]),
                                      (comp_inst $[7:7]),
                                      (comp_inst $[2:2]),
                                      (comp_inst $[11:11]),
                                      (comp_inst $[5:3])
                                      >}) in
                RetE (
                    {<
                     ({<
                       (imm $[19:19]),
                       (imm $[9:0]),
                       (imm $[10:10]),
                       (imm $[18:11])
                       >}),
                     (uncomp_inst_reg 1),
                     $$(('b"1101111") : word 7)
                     >}
            ));
          (* C.ADDIW => ADDIW checked *)
          Build_CompInst
            [["RV64C"]]
            ([
                fieldVal comp_inst_opcode_field ('b"01");
                  fieldVal comp_inst_funct3_field ('b"001")
            ])
            (fun comp_inst
             => let rd : Bit 5 @# ty := comp_inst $[11:7] in
                RetE (
                    {<
                     (ZeroExtend 6 ({< (comp_inst $[12:12]), (comp_inst $[6:2]) >})),
                     rd,
                     $$(('b"000") : word 3),
                     rd,
                     $$(('b"0011011") : word 7)
                     >}
            ));
          (* C.LI => ADDI checked *)
          Build_CompInst
            extensions_all
            ([
                fieldVal comp_inst_opcode_field ('b"01");
                  fieldVal comp_inst_funct3_field ('b"010")
            ])
            (fun comp_inst : Bit 16 @# ty
             => RetE (
                    {<
                     (ZeroExtend 6 ({< (comp_inst $[12:12]), (comp_inst $[6:2]) >})),
                     uncomp_inst_reg 0,
                     $$(('b"000") : word 3),
                     (comp_inst $[11:7]),
                     $$(('b"0010011") : word 7)
                     >}
            ));
          (*
      C.ADDI16SP and C.LUI checked
      C.ADDI16SP => ADDI checked
      C.LUI => LUI checked
           *)
          Build_CompInst
            extensions_all
            ([
                fieldVal comp_inst_opcode_field ('b"01");
                  fieldVal comp_inst_funct3_field ('b"011")
            ])
            (fun comp_inst : Bit 16 @# ty
             => let rd := (comp_inst $[11:7]) in
                RetE (
                    (ITE (rd == $$(natToWord 5 2))
                         (* C.ADDI16SP *)
                         (let imm
                              :  Bit 12 @# ty
                              := ZeroExtend 6 ({<
                                                (comp_inst $[12:12]),
                                                (comp_inst $[4:3]),
                                                (comp_inst $[5:5]),
                                                (comp_inst $[2:2]),
                                                (comp_inst $[6:6])
                                                >}) in
                          {<
                           imm,
                           uncomp_inst_reg 2,
                           $$(('b"000") : word 3),
                           uncomp_inst_reg 2,
                           $$(('b"0010011") : word 7)
                           >})
                         (* C.LUI *)
                         ({<
                           (ZeroExtend 14 ({< (comp_inst $[12:12]), (comp_inst $[6:2]) >})),
                           rd,
                           $$(('b"0110111") : word 7)
                           >}))
            ));
          (* C.SRLI => SRLI checked *)
          Build_CompInst
            extensions_all
            ([
                fieldVal comp_inst_opcode_field ('b"01");
                  fieldVal comp_inst_funct3_field ('b"100");
                  fieldVal (11, 10) ('b"00")
            ])
            (fun comp_inst : Bit 16 @# ty
             => let rd
                    :  Bit 5 @# ty
                    := comp_inst_map_reg (comp_inst $[9:7]) in
                RetE (
                    {<
                     $$(natToWord 6 0),
                     ({< (comp_inst $[12:12]), (comp_inst $[6:2]) >}),
                     rd,
                     $$(('b"101") : word 3),
                     rd, 
                     $$(('b"0010011") : word 7)
                     >}
            ));
          (* C.SRAI => SRAI checked *)
          Build_CompInst
            extensions_all
            ([
                fieldVal comp_inst_opcode_field ('b"01");
                  fieldVal comp_inst_funct3_field ('b"100");
                  fieldVal (11, 10) ('b"01")
            ])
            (fun comp_inst : Bit 16 @# ty
             => let rd
                    :  Bit 5 @# ty
                    := comp_inst_map_reg (comp_inst $[9:7]) in
                RetE (
                    {<
                     $$(('b"010000") : word 6),
                     ({< (comp_inst $[12:12]), (comp_inst $[6:2]) >}),
                     rd,
                     $$(('b"101") : word 3),
                     rd, 
                     $$(('b"0010011") : word 7)
                     >}
            ));
          (* C.ANDI => ANDI checked *)
          Build_CompInst
            extensions_all
            ([
                fieldVal comp_inst_opcode_field ('b"01");
                  fieldVal comp_inst_funct3_field ('b"100");
                  fieldVal (11, 10) ('b"10")
            ])
            (fun comp_inst : Bit 16 @# ty
             => let rd
                    :  Bit 5 @# ty
                    := comp_inst_map_reg (comp_inst $[9:7]) in
                RetE (
                    {<
                     (ZeroExtend 6 ({< (comp_inst $[12:12]), (comp_inst $[6:2]) >})),
                     rd,
                     $$(('b"111") : word 3),
                     rd, 
                     $$(('b"0010011") : word 7)
                     >}
            ));
          (* C.SUB => SUB checked *)
          Build_CompInst
            extensions_all
            ([
                fieldVal comp_inst_opcode_field ('b"01");
                  fieldVal comp_inst_funct3_field ('b"100");
                  fieldVal (6, 5) ('b"00");
                  fieldVal (11, 10) ('b"11");
                  fieldVal (12, 12) ('b"0")
            ])
            (fun comp_inst : Bit 16 @# ty
             => let rd
                    :  Bit 5 @# ty
                    := comp_inst_map_reg (comp_inst $[9:7]) in
                RetE (
                    {<
                     $$(('b"0100000") : word 7),
                     comp_inst_map_reg (comp_inst $[4:2]),
                     rd,
                     $$(('b"000") : word 3),
                     rd, 
                     $$(('b"0110011") : word 7)
                     >}
            ));
          (* C.XOR => XOR checked *)
          Build_CompInst
            extensions_all
            ([
                fieldVal comp_inst_opcode_field ('b"01");
                  fieldVal comp_inst_funct3_field ('b"100");
                  fieldVal (6, 5) ('b"01");
                  fieldVal (11, 10) ('b"11");
                  fieldVal (12, 12) ('b"0")
            ])
            (fun comp_inst : Bit 16 @# ty
             => let rd
                    :  Bit 5 @# ty
                    := comp_inst_map_reg (comp_inst $[9:7]) in
                RetE (
                    {<
                     $$(natToWord 7 0),
                     comp_inst_map_reg (comp_inst $[4:2]),
                     rd,
                     $$(('b"100") : word 3),
                     rd, 
                     $$(('b"0110011") : word 7)
                     >}
            ));
          (* C.OR => OR checked *)
          Build_CompInst
            extensions_all
            ([
                fieldVal comp_inst_opcode_field ('b"01");
                  fieldVal comp_inst_funct3_field ('b"100");
                  fieldVal (6, 5) ('b"10");
                  fieldVal (11, 10) ('b"11");
                  fieldVal (12, 12) ('b"0")
            ])
            (fun comp_inst : Bit 16 @# ty
             => let rd
                    :  Bit 5 @# ty
                    := comp_inst_map_reg (comp_inst $[9:7]) in
                RetE (
                    {<
                     $$(natToWord 7 0),
                     comp_inst_map_reg (comp_inst $[4:2]),
                     rd,
                     $$(('b"110") : word 3),
                     rd, 
                     $$(('b"0110011") : word 7)
                     >}
            ));
          (* C.AND => AND checked *)
          Build_CompInst
            extensions_all
            ([
                fieldVal comp_inst_opcode_field ('b"01");
                  fieldVal comp_inst_funct3_field ('b"100");
                  fieldVal (6, 5) ('b"11");
                  fieldVal (11, 10) ('b"11");
                  fieldVal (12, 12) ('b"0")
            ])
            (fun comp_inst : Bit 16 @# ty
             => let rd
                    :  Bit 5 @# ty
                    := comp_inst_map_reg (comp_inst $[9:7]) in
                RetE (
                    {<
                     $$(natToWord 7 0),
                     comp_inst_map_reg (comp_inst $[4:2]),
                     rd,
                     $$(('b"111") : word 3),
                     rd, 
                     $$(('b"0110011") : word 7)
                     >}
            ));
          (* C.SUBW => SUB checked *)
          Build_CompInst
            [["RV64C"]]
            ([
                fieldVal comp_inst_opcode_field ('b"01");
                  fieldVal comp_inst_funct3_field ('b"100");
                  fieldVal (6, 5) ('b"00");
                  fieldVal (11, 10) ('b"11");
                  fieldVal (12, 12) ('b"1")
            ])
            (fun comp_inst : Bit 16 @# ty
             => let rd
                    :  Bit 5 @# ty
                    := comp_inst_map_reg (comp_inst $[9:7]) in
                RetE (
                    {<
                     $$(('b"0100000") : word 7),
                     comp_inst_map_reg (comp_inst $[4:2]),
                     rd,
                     $$(('b"000") : word 3),
                     rd, 
                     $$(('b"0111011") : word 7)
                     >}
            ));
          (* C.ADDW => ADDW checked *)
          Build_CompInst
            [["RV64C"]]
            ([
                fieldVal comp_inst_opcode_field ('b"01");
                  fieldVal comp_inst_funct3_field ('b"100");
                  fieldVal (6, 5) ('b"01");
                  fieldVal (11, 10) ('b"11");
                  fieldVal (12, 12) ('b"1")
            ])
            (fun comp_inst : Bit 16 @# ty
             => let rd
                    :  Bit 5 @# ty
                    := comp_inst_map_reg (comp_inst $[9:7]) in
                RetE (
                    {<
                     $$(natToWord 7 0),
                     comp_inst_map_reg (comp_inst $[4:2]),
                     rd,
                     $$(('b"000") : word 3),
                     rd, 
                     $$(('b"0111011") : word 7)
                     >}
            ));
          (* C.J => JAL checked *)
          Build_CompInst
            extensions_all
            ([
                fieldVal comp_inst_opcode_field ('b"01");
                  fieldVal comp_inst_funct3_field ('b"101")
            ])
            (fun comp_inst
             => let imm
                    : Bit 20 @# ty
                    := ZeroExtend 9 ({<
                                      (comp_inst $[12:12]),
                                      (comp_inst $[8:8]),
                                      (comp_inst $[10:9]),
                                      (comp_inst $[6:6]),
                                      (comp_inst $[7:7]),
                                      (comp_inst $[2:2]),
                                      (comp_inst $[11:11]),
                                      (comp_inst $[5:3])
                                      >}) in
                RetE (
                    {<
                     ({<
                       (imm $[19:19]),
                       (imm $[9:0]),
                       (imm $[10:10]),
                       (imm $[18:11])
                       >}),
                     (uncomp_inst_reg 0),
                     $$(('b"1101111") : word 7)
                     >}
            ));
          (* C.BEQZ => BEQ checked *)
          Build_CompInst
            extensions_all
            ([
                fieldVal comp_inst_opcode_field ('b"01");
                  fieldVal comp_inst_funct3_field ('b"110")
            ])
            (fun comp_inst
             => let imm
                    : Bit 12 @# ty
                    := ZeroExtend 4 ({<
                                      (comp_inst $[12:12]),
                                      (comp_inst $[6:5]),
                                      (comp_inst $[2:2]),
                                      (comp_inst $[11:10]),
                                      (comp_inst $[4:3])
                                      >}) in
                RetE (
                    {<
                     ({<
                       (imm $[11:11]),
                       (imm $[9:4])
                       >}),
                     (uncomp_inst_reg 0),
                     comp_inst_map_reg (comp_inst $[9:7]),
                     $$(('b"000") : word 3),
                     ({<
                       (imm $[3:0]),
                       (imm $[10:10])
                       >}),
                     $$(('b"1100011") : word 7)
                     >}
            ));
          (* C.BNEZ => BNE checked*)
          Build_CompInst
            extensions_all
            ([
                fieldVal comp_inst_opcode_field ('b"01");
                  fieldVal comp_inst_funct3_field ('b"111")
            ])
            (fun comp_inst
             => let imm
                    : Bit 12 @# ty
                    := ZeroExtend 4 ({<
                                      (comp_inst $[12:12]),
                                      (comp_inst $[6:5]),
                                      (comp_inst $[2:2]),
                                      (comp_inst $[11:10]),
                                      (comp_inst $[4:3])
                                      >}) in
                RetE (
                    {<
                     ({<
                       (imm $[11:11]),
                       (imm $[9:4])
                       >}),
                     (uncomp_inst_reg 0),
                     comp_inst_map_reg (comp_inst $[9:7]),
                     $$(('b"001") : word 3),
                     ({<
                       (imm $[3:0]),
                       (imm $[10:10])
                       >}),
                     $$(('b"1100011") : word 7)
                     >}
            ));
          (* C.SLLI => SLLI checked *)
          Build_CompInst
            extensions_all
            ([
                fieldVal comp_inst_opcode_field ('b"10");
                  fieldVal comp_inst_funct3_field ('b"000")
            ])
            (fun comp_inst : Bit 16 @# ty
             => let rd
                    := comp_inst $[11:7] in
                RetE (
                    ({<
                      $$(natToWord 6 0),
                      ({< (comp_inst $[12:12]), (comp_inst $[6:2]) >}),
                      rd,
                      $$(('b"001") : word 3),
                      rd, 
                      $$(('b"0010011") : word 7)
                      >})
            ));
          (* C.FLDSP => FLD checked *)
          Build_CompInst
            [["RV32D"; "RV32C"];
               ["RV64D"; "RV64C"]]
            ([
                fieldVal comp_inst_opcode_field ('b"10");
                  fieldVal comp_inst_funct3_field ('b"001")
            ])
            (fun comp_inst
             => RetE (
                    {<
                     ZeroExtend 6 ({< (comp_inst $[4:2]), (comp_inst $[12:12]), (comp_inst $[6:5]) >}),
                     uncomp_inst_reg 2,
                     $$(('b"011") : word 3),
                     (comp_inst $[11:7]),
                     $$(('b"0000111") : word 7)
                     >}
            ));
          (* C.LWSP => LW checked*)
          Build_CompInst
            extensions_all
            ([
                fieldVal comp_inst_opcode_field ('b"10");
                  fieldVal comp_inst_funct3_field ('b"010")
            ])
            (fun comp_inst
             => RetE (
                    {<
                     ZeroExtend 6 ({< (comp_inst $[3:2]), (comp_inst $[12:12]), (comp_inst $[6:4]) >}),
                     uncomp_inst_reg 2,
                     $$(('b"010") : word 3),
                     (comp_inst $[11:7]),
                     $$(('b"0000011") : word 7)
                     >}
            ));
          (* C.FLWSP => FLW checked *)
          Build_CompInst
            [["RV32F"; "RV32C"]]
            ([
                fieldVal comp_inst_opcode_field ('b"10");
                  fieldVal comp_inst_funct3_field ('b"011")
            ])
            (fun comp_inst
             => RetE (
                    {<
                     ZeroExtend 6 ({< (comp_inst $[3:2]), (comp_inst $[12:12]), (comp_inst $[6:4]) >}),
                     uncomp_inst_reg 2,
                     $$(('b"010") : word 3),
                     (comp_inst $[11:7]),
                     $$(('b"0000111") : word 7)
                     >}
            ));
          (* C.LDSP => LD checked*)
          Build_CompInst
            [["RV64C"]]
            ([
                fieldVal comp_inst_opcode_field ('b"10");
                  fieldVal comp_inst_funct3_field ('b"011")
            ])
            (fun comp_inst
             => RetE (
                    {<
                     (ZeroExtend 6 ({< (comp_inst $[4:2]), (comp_inst $[12:12]), (comp_inst $[6:5]) >})),
                     uncomp_inst_reg 2,
                     $$(('b"011") : word 3),
                     (comp_inst $[11:7]),
                     $$(('b"0000011") : word 7)
                     >}
            ));
          (* C.JR and C.MV checked 
       C.JR => JALR *)
          Build_CompInst
            extensions_all
            ([
                fieldVal comp_inst_opcode_field ('b"10");
                  fieldVal comp_inst_funct3_field ('b"100");
                  fieldVal (12, 12) ('b"0")
            ])
            (fun comp_inst
             => RetE (
                    ITE ((comp_inst $[6:2]) == $0)
                        (* C.JR checked *)
                        ({<
                          $$(natToWord 12 0),
                          (comp_inst $[11:7]),
                          $$(('b"000") : word 3),
                          uncomp_inst_reg 0,
                          $$(('b"1100111") : word 7)
                          >})
                        (* C.MV checked *)
                        ({<
                          $$(('b"0000000") : word 7),
                          (comp_inst $[6:2]),
                          uncomp_inst_reg 0,
                          $$(('b"000") : word 3),
                          (comp_inst $[11:7]),
                          $$(('b"0110011") : word 7)
                          >})
            ));
          (*
       C.ADD, C.EBREAK, and C.JALR checked
       C.EBREAK => EBREAK
       C.JALR => JALR
           *)
          Build_CompInst
            extensions_all
            ([
                fieldVal comp_inst_opcode_field ('b"10");
                  fieldVal comp_inst_funct3_field ('b"100");
                  fieldVal (12, 12) ('b"1")
            ])
            (fun comp_inst
             => RetE (
                    ITE ((comp_inst $[6:2]) == $0)
                        (ITE ((comp_inst $[11:7]) == $0)
                             (* C.EBREAK checked *)
                             ({<
                               $$(('b"000000000001") : word 12),
                               $$(natToWord 13 0),
                               $$(('b"1110011") : word 7)
                               >})
                             (* C.JALR checked *)
                             ({<
                               $$(natToWord 12 0),
                               (comp_inst $[11:7]),
                               $$(('b"000") : word 3),
                               uncomp_inst_reg 1,
                               $$(('b"1100111") : word 7)
                               >}))
                        (* C.ADD checked *)
                        (let rd := comp_inst $[11:7] in
                         ({<
                           $$(natToWord 7 0),
                           (comp_inst $[6:2]),
                           rd,
                           $$(('b"000") : word 3),
                           rd,
                           $$(('b"0110011") : word 7)
                           >}))
            ));
          (* C.FSDSP => FSD checked *)
          Build_CompInst
            [["RV32D"; "RV32C"];
               ["RV64D"; "RV64C"]]
            ([
                fieldVal comp_inst_opcode_field ('b"10");
                  fieldVal comp_inst_funct3_field ('b"101")
            ])
            (fun comp_inst
             => let imm := ZeroExtend 6 ({< (comp_inst $[9:7]), (comp_inst $[12:10]) >}) in
                RetE (
                    ({<
                      (imm $[11:5]),
                      (comp_inst $[6:2]),
                      (uncomp_inst_reg 2),
                      $$(('b"011") : word 3),
                      (imm $[4:0]),
                      $$(('b"0100111") : word 7)
                      >})
            ));
          (* C.SWSP => SW checked *)
          Build_CompInst
            extensions_all
            ([
                fieldVal comp_inst_opcode_field ('b"10");
                  fieldVal comp_inst_funct3_field ('b"110")
            ])
            (fun comp_inst
             => let imm := ZeroExtend 6 ({< (comp_inst $[8:7]), (comp_inst $[12:9]) >}) in
                RetE (
                    ({<
                      (imm $[11:5]),
                      (comp_inst $[6:2]),
                      (uncomp_inst_reg 2),
                      $$(('b"010") : word 3),
                      (imm $[4:0]),
                      $$(('b"0100011") : word 7)
                      >})
            ));
          (* C.FSWSP => FSW checked *)
          Build_CompInst
            [["RV32F"; "RV32C"]]
            ([
                fieldVal comp_inst_opcode_field ('b"10");
                  fieldVal comp_inst_funct3_field ('b"111")
            ])
            (fun comp_inst
             => let imm := ZeroExtend 6 ({< (comp_inst $[8:7]), (comp_inst $[12:9]) >}) in
                RetE (
                    ({<
                      (imm $[11:5]),
                      (comp_inst $[6:2]),
                      (uncomp_inst_reg 2),
                      $$(('b"010") : word 3),
                      (imm $[4:0]),
                      $$(('b"0100111") : word 7)
                      >})
            ));
          (* C.SDSP => SD checked *)
          Build_CompInst
            [["RV64C"]]
            ([
                fieldVal comp_inst_opcode_field ('b"10");
                  fieldVal comp_inst_funct3_field ('b"111")
            ])
            (fun comp_inst
             => let imm := ZeroExtend 6 ({< (comp_inst $[9:7]), (comp_inst $[12:10]) >}) in
                RetE (
                    ({<
                      (imm $[11:5]),
                      (comp_inst $[6:2]),
                      (uncomp_inst_reg 2),
                      $$(('b"011") : word 3),
                      (imm $[4:0]),
                      $$(('b"0100011") : word 7)
                      >})
            ))
      ]. 

End database.
