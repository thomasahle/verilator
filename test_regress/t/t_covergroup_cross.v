// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test covergroup cross coverage functionality
//
// Note: Verilator cross coverage semantics - cross bins are hit when
// both component bins have EVER been hit (accumulated), not necessarily
// in the same sample. This provides useful "have both bins been exercised"
// coverage information.

module t;
   bit [1:0] a;
   bit [1:0] b;

   covergroup cg;
      A_CP: coverpoint a {
         bins low = {[0:1]};
         bins high = {[2:3]};
      }
      B_CP: coverpoint b {
         bins low = {[0:1]};
         bins high = {[2:3]};
      }
      AXB: cross A_CP, B_CP;
   endgroup

   cg cg_inst;
   real coverage_pct;

   initial begin
      cg_inst = new;

      // Before sampling - 0%
      coverage_pct = cg_inst.get_inst_coverage();
      $display("Coverage before sampling: %0.2f%%", coverage_pct);

      // Sample a=0 (low), b=0 (low)
      // Hits: A_CP.low, B_CP.low, AXB_low_low
      // Total: 3 of 8 bins = 37.5%
      a = 0; b = 0;
      cg_inst.sample();

      coverage_pct = cg_inst.get_inst_coverage();
      $display("After a=0,b=0: %0.2f%%", coverage_pct);
      if (coverage_pct != 37.5) begin
         $display("ERROR: Expected 37.5%%, got %0.2f%%", coverage_pct);
         $stop;
      end

      // Sample a=3 (high), b=3 (high)
      // New hits: A_CP.high, B_CP.high, AXB_high_high
      // Cross coverage: since A_CP.low && B_CP.high both hit, AXB_low_high fires
      //                 since A_CP.high && B_CP.low both hit, AXB_high_low fires
      // Total: all 8 bins hit = 100%
      a = 3; b = 3;
      cg_inst.sample();

      coverage_pct = cg_inst.get_inst_coverage();
      $display("After a=3,b=3: %0.2f%%", coverage_pct);
      if (coverage_pct != 100.0) begin
         $display("ERROR: Expected 100%%, got %0.2f%%", coverage_pct);
         $stop;
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
