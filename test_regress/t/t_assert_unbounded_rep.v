// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test unbounded sequence repetition [*] and [+] parsing

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   int cyc = 0;
   logic valid;
   logic ready;
   logic done;

   // Property with unbounded repetition [*] - zero or more
   // Note: Full semantics not implemented, just parsing
   property p_zero_or_more;
      @(posedge clk) valid[*] |-> ready;
   endproperty
   // Don't assert - semantics are simplified
   // cover property (p_zero_or_more);

   // Property with unbounded repetition [+] - one or more
   property p_one_or_more;
      @(posedge clk) valid[+] |-> ready;
   endproperty
   // Don't assert - semantics are simplified
   // cover property (p_one_or_more);

   always @(posedge clk) begin
      cyc <= cyc + 1;
      valid <= 1'b1;
      ready <= 1'b1;
      done <= 1'b0;

      if (cyc == 10) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
