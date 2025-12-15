// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test for SVA consecutive repetition [*n]

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   int   cyc = 0;
   logic a, b;

   // Consecutive repetition: a[*3] means a is true for 3 consecutive cycles
   property p_consec_rep;
      @(posedge clk)
      $rose(a) |-> a[*3];
   endproperty

   // Range repetition: a[*2:4] means a is true for 2 to 4 consecutive cycles
   property p_range_rep;
      @(posedge clk)
      $rose(b) |-> b[*2:4];
   endproperty

   assert property (p_consec_rep)
      else $error("p_consec_rep failed at cyc=%0d", cyc);

   assert property (p_range_rep)
      else $error("p_range_rep failed at cyc=%0d", cyc);

   always @(posedge clk) begin
      cyc <= cyc + 1;

      case (cyc)
         0: begin a <= 0; b <= 0; end
         1: begin a <= 0; b <= 0; end
         // Test a[*3] - a high for 3 cycles
         2: begin a <= 1; end  // rose
         3: begin a <= 1; end
         4: begin a <= 1; end
         5: begin a <= 0; end
         // Test b[*2:4] - b high for 2-4 cycles
         6: begin b <= 1; end  // rose
         7: begin b <= 1; end
         8: begin b <= 1; end
         9: begin b <= 0; end
         11: begin
            $write("*-* All Finished *-*\n");
            $finish;
         end
         default: begin end
      endcase
   end

endmodule
