/*
  This module simulates a 32 bit register file attached to a processor core.
*/
module register32 (
  input         clk,
  input         reset,
  input         in_write_enable,
  input [4:0]   in_write_register_select,
  input [4:0]   in_read_register_select_0,
  input [4:0]   in_read_register_select_1,
  input [4:0]   in_read_register_select_2,
  input [63:0]  in_write_data,
  output [63:0] out_read_data_0,
  output [63:0] out_read_data_1,
  output [63:0] out_read_data_2
);

parameter integer num_registers = 32;
reg [63:0] register_bank [(num_registers - 1):0];

// load operations.
assign out_read_data_0 = register_bank [in_read_register_select_0];
assign out_read_data_1 = register_bank [in_read_register_select_1];
assign out_read_data_2 = register_bank [in_read_register_select_2];

// store operations.
always @(posedge clk)
begin
  if (in_write_enable && !reset)
  begin
    register_bank [in_write_register_select] <= in_write_data;
  end
end
endmodule
