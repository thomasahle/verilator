// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test property case expression (IEEE 1800-2017 16.12)

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   int   count = 0;
   logic [1:0] state;
   logic req, ack, err;

   always @(posedge clk) begin
      count <= count + 1;
      state <= count[1:0];
      req <= (count == 2);
      ack <= (count == 3);
      err <= 0;
   end

   // Property using case expression (IEEE 1800-2017 requires semicolons)
   property p_state_check;
      @(posedge clk)
      case (state)
         2'b00: !err;
         2'b01: 1'b1;
         2'b10, 2'b11: 1'b1;
         default: 1'b1;
      endcase
   endproperty

   assert property (p_state_check);

   // Simple property case
   property p_simple_case;
      @(posedge clk)
      case (state[0])
         1'b0: 1'b1;
         1'b1: 1'b1;
      endcase
   endproperty

   assert property (p_simple_case);

   initial begin
      repeat(10) @(posedge clk);
      $write("*-* All Coverage Points Covered *-*\n");
      $finish;
   end

endmodule
