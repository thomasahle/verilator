// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test covergroup get_inst_coverage() function
// Note: get_coverage() is static (type-level coverage), returns 0.0 placeholder
//       get_inst_coverage() is instance method (instance-level coverage)

module t;
   int data;

   covergroup cg;
      DATA_CP: coverpoint data {
         bins low = {[0:3]};
         bins high = {[4:7]};
      }
   endgroup

   cg cg_inst;
   real coverage_pct;

   initial begin
      cg_inst = new;

      // Before sampling - coverage should be 0%
      coverage_pct = cg_inst.get_inst_coverage();
      $display("Coverage before sampling: %0.2f%%", coverage_pct);

      // Sample low bin
      data = 2;
      cg_inst.sample();

      // After sampling one bin - coverage should be ~50%
      coverage_pct = cg_inst.get_inst_coverage();
      $display("Coverage after sampling low: %0.2f%%", coverage_pct);

      // Sample high bin
      data = 5;
      cg_inst.sample();

      // After sampling both bins - coverage should be 100%
      coverage_pct = cg_inst.get_inst_coverage();
      $display("Coverage after sampling both: %0.2f%%", coverage_pct);

      // Check coverage is 100% (both bins hit)
      if (coverage_pct == 100.0) begin
         $write("*-* All Finished *-*\n");
      end else begin
         $display("Expected 100%% coverage, got %0.2f%%", coverage_pct);
      end
      $finish;
   end
endmodule
