// DESCRIPTION: Verilator: Test assertion statistics tracking
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

   // Generate clock
   reg clk = 0;
   always #5 clk = ~clk;

   integer cyc = 0;
   logic a = 1, b = 0;

   // Concurrent assertions with labels
   property p_always_a;
      @(posedge clk) a == 1'b1;
   endproperty

   assert_a: assert property (p_always_a);

   property p_never_both_zero;
      @(posedge clk) !(a == 1'b0 && b == 1'b0);
   endproperty

   assert_never_zero: assert property (p_never_both_zero);

   always @(posedge clk) begin
      cyc <= cyc + 1;

      // Drive signals to exercise assertions
      case (cyc)
         0: begin a <= 1; b <= 0; end
         1: begin a <= 1; b <= 1; end
         2: begin a <= 1; b <= 0; end
         3: begin a <= 1; b <= 1; end
         4: begin a <= 1; b <= 0; end
         5: begin
            $write("*-* All Finished *-*\n");
            $finish;
         end
         default: begin a <= 1; b <= 0; end
      endcase
   end

endmodule
