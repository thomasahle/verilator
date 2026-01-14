// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test SVA range delays ##[n:m]
// Tests that (a ##[1:3] b) matches b at any cycle in the range [1,3]

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;
   int cyc = 0;
   logic a, b, c;
   int fail_count = 0;

   // Test range delay: b at cycle 7 (2 cycles after a at 5) is within [1:3]
   // Since c=0, if sequence matches, assertion should fail (which is what we want to test)
   property p_range;
      @(posedge clk) (a ##[1:3] b) |-> c;
   endproperty
   assert property (p_range) else begin
      fail_count = fail_count + 1;
   end

   always @(posedge clk) begin
      cyc <= cyc + 1;
      a <= 0;
      b <= 0;
      c <= 0;  // c always false

      // a at cycle 5, b at cycle 7 (2 cycles later, within [1:3])
      if (cyc == 5) a <= 1;
      if (cyc == 7) b <= 1;

      if (cyc >= 15) begin
         // With correct range delay: b at 2 cycles after a is within [1:3]
         // so sequence matches, and since c=0, assertion fails
         // fail_count should be > 0
         if (fail_count == 0) begin
            $write("%%Error: Range delay ##[1:3] not working - treated as ##1\n");
            $stop;
         end else begin
            $write("*-* All Finished *-*\n");
            $finish;
         end
      end
   end
endmodule
