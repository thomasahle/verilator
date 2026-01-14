// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test non-consecutive sequence repetition [=n] parsing

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   int cyc = 0;
   logic valid;
   logic ready;

   // Property with non-consecutive repetition [=n]
   // Note: Full semantics not implemented, just parsing
   property p_nonconsec_exact;
      @(posedge clk) valid[=3] |-> ready;
   endproperty
   // Don't assert - semantics are simplified
   // cover property (p_nonconsec_exact);

   // Property with non-consecutive range [=m:n]
   property p_nonconsec_range;
      @(posedge clk) valid[=2:5] |-> ready;
   endproperty
   // Don't assert - semantics are simplified
   // cover property (p_nonconsec_range);

   always @(posedge clk) begin
      cyc <= cyc + 1;
      valid <= 1'b1;
      ready <= 1'b1;

      if (cyc == 10) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
