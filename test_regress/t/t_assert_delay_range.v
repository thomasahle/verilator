// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test range cycle delay ##[m:n] and ##[1:$] (unbounded)

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   int cyc = 0;
   logic a, b, c;

   // Property with bounded range delay ##[1:3]
   property p_bounded_range;
      @(posedge clk) a |-> ##[1:3] b;
   endproperty

   // Property with unbounded range delay ##[1:$]
   property p_unbounded_range;
      @(posedge clk) a |-> ##[1:$] c;
   endproperty

   always @(posedge clk) begin
      cyc <= cyc + 1;
      a <= (cyc == 2);
      b <= (cyc >= 3 && cyc <= 5);
      c <= (cyc == 5);

      if (cyc == 10) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
