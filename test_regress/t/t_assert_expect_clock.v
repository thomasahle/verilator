// DESCRIPTION: Verilator: Test expect with clocking inside procedure
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// This test verifies expect assertions with clocking events work
// inside procedural blocks (initial/always)

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   logic a, b;
   integer cyc;

   initial cyc = 0;

   always @(posedge clk) begin
      cyc <= cyc + 1;
      a <= cyc[0];
      b <= cyc[1];
   end

   // Expect with clocking event inside initial block
   initial begin
      // Wait for some cycles
      repeat(5) @(posedge clk);

      // Expect statement with clocking - this was causing UNSUPPORTED error
      expect(@(posedge clk) a |-> ##1 b)
        else $error("Expect failed");

      // More cycles
      repeat(5) @(posedge clk);

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
