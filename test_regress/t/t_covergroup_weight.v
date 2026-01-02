// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test for option.weight - controls contribution to coverage

module t;
   int value;

   // Covergroup with weight=0: should always report 0% coverage
   covergroup cg_zero_weight;
      option.weight = 0;
      cp_value: coverpoint value {
         bins low = {[0:3]};
         bins mid = {[4:7]};
         bins high = {[8:11]};
      }
   endgroup

   // Covergroup with default weight (1): should report actual coverage
   covergroup cg_default_weight;
      cp_value: coverpoint value {
         bins low = {[0:3]};
         bins mid = {[4:7]};
         bins high = {[8:11]};
      }
   endgroup

   cg_zero_weight cg_zero;
   cg_default_weight cg_default;

   initial begin
      cg_zero = new;
      cg_default = new;

      // Sample same values for both covergroups
      value = 2;  // low bin
      cg_zero.sample();
      cg_default.sample();

      value = 5;  // mid bin
      cg_zero.sample();
      cg_default.sample();

      // Check zero-weight covergroup - should be 0%
      $display("Zero weight coverage: %0.1f%%", cg_zero.get_inst_coverage());
      if (cg_zero.get_inst_coverage() > 0.1) begin
         $display("%%Error: Zero-weight covergroup should report 0%% coverage");
         $stop;
      end

      // Check default-weight covergroup - should be ~66.7% (2/3 bins)
      $display("Default weight coverage: %0.1f%%", cg_default.get_inst_coverage());
      if (cg_default.get_inst_coverage() < 60.0 || cg_default.get_inst_coverage() > 70.0) begin
         $display("%%Error: Default-weight covergroup should report ~66.7%% coverage");
         $stop;
      end

      $display("*-* All Finished *-*");
      $finish;
   end
endmodule
