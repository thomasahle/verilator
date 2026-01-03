// DESCRIPTION: Verilator: Test for bins array (bins x[] = {...}) syntax
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

   // Test bins array expansion: bins arr[] = {[0:3]} should create 4 separate bins
   // arr[0] for value 0, arr[1] for value 1, etc.

   int value;

   // Covergroup with bins array
   covergroup cg;
      cp: coverpoint value {
         bins arr[] = {[0:3]};  // Should create 4 separate bins: arr[0], arr[1], arr[2], arr[3]
      }
   endgroup

   // Covergroup with explicit bins for comparison
   covergroup cg_explicit;
      cp: coverpoint value {
         bins bin0 = {0};
         bins bin1 = {1};
         bins bin2 = {2};
         bins bin3 = {3};
      }
   endgroup

   cg cg_inst;
   cg_explicit cg_expl;

   initial begin
      cg_inst = new;
      cg_expl = new;

      // Initially 0% coverage
      if (cg_inst.get_inst_coverage() != 0.0) begin
         $display("FAILED: Expected 0%% initially, got %f%%", cg_inst.get_inst_coverage());
         $stop;
      end

      // Sample value 1 - should give 25% (1/4 bins)
      value = 1;
      cg_inst.sample();
      cg_expl.sample();

      if (cg_inst.get_inst_coverage() < 24.0 || cg_inst.get_inst_coverage() > 26.0) begin
         $display("FAILED: bins array expected 25%% after hitting 1/4 bins, got %f%%", cg_inst.get_inst_coverage());
         $stop;
      end
      if (cg_expl.get_inst_coverage() < 24.0 || cg_expl.get_inst_coverage() > 26.0) begin
         $display("FAILED: explicit bins expected 25%% after hitting 1/4 bins, got %f%%", cg_expl.get_inst_coverage());
         $stop;
      end

      // Sample value 2 - should give 50% (2/4 bins)
      value = 2;
      cg_inst.sample();
      cg_expl.sample();

      if (cg_inst.get_inst_coverage() < 49.0 || cg_inst.get_inst_coverage() > 51.0) begin
         $display("FAILED: bins array expected 50%% after hitting 2/4 bins, got %f%%", cg_inst.get_inst_coverage());
         $stop;
      end

      // Sample all 4 values - should give 100%
      value = 0;
      cg_inst.sample();
      cg_expl.sample();
      value = 3;
      cg_inst.sample();
      cg_expl.sample();

      if (cg_inst.get_inst_coverage() < 99.0 || cg_inst.get_inst_coverage() > 101.0) begin
         $display("FAILED: bins array expected 100%% after hitting 4/4 bins, got %f%%", cg_inst.get_inst_coverage());
         $stop;
      end
      if (cg_expl.get_inst_coverage() < 99.0 || cg_expl.get_inst_coverage() > 101.0) begin
         $display("FAILED: explicit bins expected 100%% after hitting 4/4 bins, got %f%%", cg_expl.get_inst_coverage());
         $stop;
      end

      $display("PASSED: bins array expansion working correctly");
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
