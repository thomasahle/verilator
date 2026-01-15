// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026.
// SPDX-License-Identifier: CC0-1.0

// Test for SVA cover sequence statement

module t;
   logic clk = 0;
   always #5 clk = ~clk;

   int   cyc = 0;
   logic a, b, c;

   // Simple cover sequence
   cover sequence (@(posedge clk) a ##1 b)
      $display("Covered: a ##1 b at cyc=%0d", cyc);

   // Cover sequence with disable iff
   cover sequence (@(posedge clk) disable iff (cyc < 2) b ##1 c)
      $display("Covered: b ##1 c at cyc=%0d", cyc);

   // Cover sequence with multiple cycles
   cover sequence (@(posedge clk) a ##[1:3] c)
      $display("Covered: a ##[1:3] c at cyc=%0d", cyc);

   always @(posedge clk) begin
      cyc <= cyc + 1;

      case (cyc)
         0: begin a <= 0; b <= 0; c <= 0; end
         1: begin a <= 1; b <= 0; c <= 0; end  // Start sequence a
         2: begin a <= 0; b <= 1; c <= 0; end  // a ##1 b should match
         3: begin a <= 0; b <= 0; c <= 1; end  // b ##1 c should match
         4: begin a <= 1; b <= 0; c <= 0; end  // Start a again
         5: begin a <= 0; b <= 0; c <= 0; end
         6: begin a <= 0; b <= 0; c <= 1; end  // a ##[1:3] c should match
         7: begin a <= 0; b <= 0; c <= 0; end
         8: begin
            $write("*-* All Finished *-*\n");
            $finish;
         end
         default: begin end
      endcase
   end

endmodule
