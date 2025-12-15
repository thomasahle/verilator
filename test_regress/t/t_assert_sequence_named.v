// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test for named sequence declarations with clocked bodies
// IEEE 1800-2017 16.8: Declaring sequences

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   int   cyc = 0;
   logic a, b, c, d;

   // Named sequence with clocked body - simple expression (no cycle delays)
   // This pattern is commonly used in SPI VIP assertions
   sequence seq_a_and_b;
      @(posedge clk)
      a && b;
   endsequence

   // Named sequence without explicit clock
   sequence seq_c_or_d;
      c || d;
   endsequence

   // Named sequence with condition check
   sequence seq_cs_low;
      @(posedge clk)
      (a == 0);  // Check chip select low
   endsequence

   // Assertions using inline expressions
   assert property (@(posedge clk) disable iff (cyc < 2)
      a |-> b) else $error("a |-> b failed at cyc=%0d", cyc);

   always @(posedge clk) begin
      cyc <= cyc + 1;

      // Create test pattern
      case (cyc)
         0: begin a <= 0; b <= 0; c <= 0; d <= 0; end
         1: begin a <= 1; b <= 1; c <= 1; d <= 0; end
         2: begin a <= 1; b <= 1; c <= 0; d <= 1; end  // a->b satisfied
         3: begin a <= 0; b <= 0; c <= 1; d <= 0; end
         4: begin a <= 1; b <= 1; c <= 0; d <= 1; end  // a->b satisfied
         5: begin a <= 0; b <= 0; c <= 0; d <= 0; end
         10: begin
            $write("*-* All Coverage Coverage *-*\n");
            $finish;
         end
         default: ;
      endcase
   end

endmodule
