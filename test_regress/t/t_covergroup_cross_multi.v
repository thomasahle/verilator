// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test covergroup cross coverage with 3+ coverpoints

module t;
   bit [1:0] a;
   bit [1:0] b;
   bit [1:0] c;

   covergroup cg;
      A_CP: coverpoint a {
         bins low = {[0:1]};
         bins high = {[2:3]};
      }
      B_CP: coverpoint b {
         bins low = {[0:1]};
         bins high = {[2:3]};
      }
      C_CP: coverpoint c {
         bins low = {[0:1]};
         bins high = {[2:3]};
      }
      // 3-way cross: 2*2*2 = 8 cross bins
      AXBXC: cross A_CP, B_CP, C_CP;
   endgroup

   cg cg_inst;
   real coverage_pct;

   initial begin
      cg_inst = new;

      // Before sampling - 0%
      // Total bins: 6 coverpoint bins + 8 cross bins = 14
      coverage_pct = cg_inst.get_inst_coverage();
      $display("Coverage before sampling: %0.2f%%", coverage_pct);
      if (coverage_pct != 0.0) begin
         $display("ERROR: Expected 0%%, got %0.2f%%", coverage_pct);
         $stop;
      end

      // Sample a=0 (low), b=0 (low), c=0 (low)
      // Hits: A_CP.low, B_CP.low, C_CP.low, AXBXC_low_low_low
      // Total: 4 of 14 bins = 28.57%
      a = 0; b = 0; c = 0;
      cg_inst.sample();

      coverage_pct = cg_inst.get_inst_coverage();
      $display("After a=0,b=0,c=0: %0.2f%%", coverage_pct);
      // 4/14 = 28.571...
      if (coverage_pct < 28.5 || coverage_pct > 28.6) begin
         $display("ERROR: Expected ~28.57%%, got %0.2f%%", coverage_pct);
         $stop;
      end

      // Sample a=3 (high), b=3 (high), c=3 (high)
      // New direct hits: A_CP.high, B_CP.high, C_CP.high, AXBXC_high_high_high
      // Cross bins now hit (since all coverpoint bins have been hit at some point):
      // AXBXC_low_low_high, AXBXC_low_high_low, AXBXC_low_high_high,
      // AXBXC_high_low_low, AXBXC_high_low_high, AXBXC_high_high_low
      // Total: all 14 bins hit = 100%
      a = 3; b = 3; c = 3;
      cg_inst.sample();

      coverage_pct = cg_inst.get_inst_coverage();
      $display("After a=3,b=3,c=3: %0.2f%%", coverage_pct);
      if (coverage_pct != 100.0) begin
         $display("ERROR: Expected 100%%, got %0.2f%%", coverage_pct);
         $stop;
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
