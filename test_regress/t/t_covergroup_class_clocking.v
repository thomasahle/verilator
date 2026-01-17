// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test covergroup clocking events inside classes with automatic sampling
// The clocking event references a class member variable

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   int cyc = 0;

   class CgCls;
      int m_clk;  // Class member used as clocking event
      int m_val;  // Coverpoint variable

      // Covergroup with clocking event referencing class member
      covergroup cov1 @(posedge m_clk);
         coverpoint m_val { bins low = {[0:3]}; bins high = {[4:7]}; }
      endgroup

      function new();
         cov1 = new;
      endfunction
   endclass

   CgCls obj;

   initial begin
      obj = new;
   end

   always @(posedge clk) begin
      cyc <= cyc + 1;
      if (cyc < 10) begin
         obj.m_val <= cyc % 8;
         // Toggle m_clk to trigger automatic sampling
         obj.m_clk <= ~obj.m_clk;
      end
      if (cyc == 15) begin
         // Coverage should be non-zero from automatic sampling
         $display("Coverage: %0.2f%%", obj.cov1.get_inst_coverage());
         if (obj.cov1.get_inst_coverage() > 0) begin
            $write("*-* All Finished *-*\n");
            $finish;
         end else begin
            $display("FAILED: Coverage is zero");
            $stop;
         end
      end
   end
endmodule
