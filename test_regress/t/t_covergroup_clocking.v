// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test covergroup clocking events with automatic sampling

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   int a;
   int b;
   int cyc = 0;

   // Covergroup with clocking event - automatically samples on posedge clk
   covergroup cg_auto @(posedge clk);
      coverpoint a { bins low = {[0:3]}; bins high = {[4:7]}; }
      coverpoint b { bins low = {[0:3]}; bins high = {[4:7]}; }
   endgroup

   cg_auto cov1;

   initial begin
      cov1 = new;
   end

   always @(posedge clk) begin
      cyc <= cyc + 1;
      if (cyc < 10) begin
         a <= cyc % 8;
         b <= (cyc + 1) % 8;
         // No manual sample() needed - automatic sampling handles it
      end
      if (cyc == 15) begin
         // Coverage should be non-zero from automatic sampling
         $display("Coverage: %0.2f%%", cov1.get_inst_coverage());
         if (cov1.get_inst_coverage() > 0) begin
            $write("*-* All Finished *-*\n");
            $finish;
         end else begin
            $display("FAILED: Coverage is zero");
            $stop;
         end
      end
   end
endmodule
