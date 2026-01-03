// DESCRIPTION: Verilator: Test for option.goal in covergroups
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

   // Test option.goal - sets coverage goal percentage
   // When goal < 100, coverage is scaled up so hitting 'goal' percent gives 100%

   int value;

   // Covergroup with option.goal = 50
   // Hitting 50% of bins should give 100% coverage
   covergroup cg_goal50;
      option.goal = 50;
      cp: coverpoint value {
         bins bin0 = {0};
         bins bin1 = {1};
         bins bin2 = {2};
         bins bin3 = {3};
      }
   endgroup

   // Covergroup with default goal (100)
   covergroup cg_goal100;
      cp: coverpoint value {
         bins bin0 = {0};
         bins bin1 = {1};
         bins bin2 = {2};
         bins bin3 = {3};
      }
   endgroup

   cg_goal50 cg50;
   cg_goal100 cg100;

   initial begin
      cg50 = new;
      cg100 = new;

      // Sample 2 out of 4 bins (50% actual coverage)
      value = 0;
      cg50.sample();
      cg100.sample();

      value = 1;
      cg50.sample();
      cg100.sample();

      // For cg_goal50 (goal=50): hitting 50% = 100% coverage
      // For cg_goal100 (goal=100): hitting 50% = 50% coverage
      $display("After hitting 2/4 bins:");
      $display("  cg_goal50 (goal=50): %f%%", cg50.get_inst_coverage());
      $display("  cg_goal100 (goal=100): %f%%", cg100.get_inst_coverage());

      // Verify cg_goal50 gives 100% (50% / 50 * 100 = 100%)
      if (cg50.get_inst_coverage() >= 99.0 && cg50.get_inst_coverage() <= 101.0) begin
         $display("PASSED: goal=50 gives 100%% when hitting 50%% of bins");
      end else begin
         $display("FAILED: goal=50 expected 100%%, got %f%%", cg50.get_inst_coverage());
         $stop;
      end

      // Verify cg_goal100 gives 50%
      if (cg100.get_inst_coverage() >= 49.0 && cg100.get_inst_coverage() <= 51.0) begin
         $display("PASSED: goal=100 gives 50%% when hitting 50%% of bins");
      end else begin
         $display("FAILED: goal=100 expected 50%%, got %f%%", cg100.get_inst_coverage());
         $stop;
      end

      // Now sample all 4 bins - both should show 100%
      value = 2;
      cg50.sample();
      cg100.sample();

      value = 3;
      cg50.sample();
      cg100.sample();

      $display("After hitting 4/4 bins:");
      $display("  cg_goal50 (goal=50): %f%%", cg50.get_inst_coverage());
      $display("  cg_goal100 (goal=100): %f%%", cg100.get_inst_coverage());

      // Both should be 100% (cg_goal50 is capped at 100%)
      if (cg50.get_inst_coverage() >= 99.0 && cg50.get_inst_coverage() <= 101.0) begin
         $display("PASSED: goal=50 capped at 100%% when exceeding goal");
      end else begin
         $display("FAILED: goal=50 should be capped at 100%%, got %f%%", cg50.get_inst_coverage());
         $stop;
      end

      if (cg100.get_inst_coverage() >= 99.0 && cg100.get_inst_coverage() <= 101.0) begin
         $display("PASSED: goal=100 gives 100%% when hitting 100%% of bins");
      end else begin
         $display("FAILED: goal=100 expected 100%%, got %f%%", cg100.get_inst_coverage());
         $stop;
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
