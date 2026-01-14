// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test for option.at_least - minimum hit count for bin to be considered covered

module t;
   int value;

   // Covergroup with at_least=3: bins only count as covered after 3 hits
   covergroup cg;
      option.at_least = 3;
      cp_value: coverpoint value {
         bins low = {[0:3]};
         bins mid = {[4:7]};
         bins high = {[8:11]};
      }
   endgroup

   cg cg_inst;

   initial begin
      cg_inst = new;

      // Sample value=5 only twice - should NOT count as covered (need 3)
      value = 5;
      cg_inst.sample();
      cg_inst.sample();

      // Check coverage - should be 0% (no bins reached at_least threshold)
      $display("After 2 samples of mid: Coverage = %0.1f%%", cg_inst.get_inst_coverage());
      if (cg_inst.get_inst_coverage() > 0.1) begin
         $display("%%Error: Coverage should be 0%% after 2 samples with at_least=3");
         $stop;
      end

      // Sample once more - now mid bin should be covered
      cg_inst.sample();
      $display("After 3 samples of mid: Coverage = %0.1f%%", cg_inst.get_inst_coverage());

      // Now try low bin - sample 3 times
      value = 2;
      cg_inst.sample();
      cg_inst.sample();
      cg_inst.sample();
      $display("After 3 samples of low: Coverage = %0.1f%%", cg_inst.get_inst_coverage());

      // And high bin - sample 3 times
      value = 10;
      cg_inst.sample();
      cg_inst.sample();
      cg_inst.sample();
      $display("After 3 samples of high: Coverage = %0.1f%%", cg_inst.get_inst_coverage());

      // Now all 3 bins should be covered (100%)
      if (cg_inst.get_inst_coverage() < 99.0) begin
         $display("%%Error: Coverage should be 100%% after all bins sampled 3+ times");
         $stop;
      end

      $display("*-* All Finished *-*");
      $finish;
   end
endmodule
