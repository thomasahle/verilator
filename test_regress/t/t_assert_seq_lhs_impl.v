// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test SVA sequence on LHS of implication operator
// This tests the pattern: (expr ##n expr) |-> expr

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;
   int cyc = 0;
   logic a, b, c;

   // Simple sequence on LHS
   property p_seq_lhs_simple;
      @(posedge clk) (a ##1 b) |-> c;
   endproperty
   assert property (p_seq_lhs_simple) else $error("p_seq_lhs_simple failed at cyc=%0d", cyc);

   always @(posedge clk) begin
      cyc <= cyc + 1;

      // Ensure all values are explicitly set to avoid X
      a <= 0;
      b <= 0;
      c <= 1;  // Keep c high so implication passes

      // Simple test pattern
      if (cyc == 5) begin
         // Set up sequence: a=1 at cyc 5, b=1 at cyc 6
         a <= 1;
      end
      if (cyc == 6) begin
         b <= 1;  // Sequence matches, check c (which is 1, so pass)
      end

      if (cyc >= 20) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
