// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test class-embedded covergroups with enclosing scope access
// IEEE 1800-2017 19.4

module t;
   // Enclosing class with a covergroup member
   class Config;
      bit [7:0] mode;
      bit [3:0] level;
   endclass

   class Coverage;
      Config cfg;

      // Covergroup declared inside class - should access enclosing class members
      covergroup cg;
         MODE_CP: coverpoint cfg.mode {
            bins low = {[0:127]};
            bins high = {[128:255]};
         }
         LEVEL_CP: coverpoint cfg.level {
            bins l0 = {[0:3]};
            bins l1 = {[4:7]};
            bins l2 = {[8:11]};
            bins l3 = {[12:15]};
         }
      endgroup

      function new();
         cfg = new;
         cg = new;
      endfunction

      function void sample_data();
         cg.sample();
      endfunction

      function real get_cov();
         return cg.get_inst_coverage();
      endfunction
   endclass

   Coverage cov;
   real coverage_pct;

   initial begin
      cov = new;

      // Before sampling
      coverage_pct = cov.get_cov();
      $display("Coverage before sampling: %0.2f%%", coverage_pct);

      // Sample with low mode and level
      cov.cfg.mode = 50;
      cov.cfg.level = 2;
      cov.sample_data();

      coverage_pct = cov.get_cov();
      $display("After sample(mode=50,level=2): %0.2f%%", coverage_pct);

      // Sample with high mode
      cov.cfg.mode = 200;
      cov.cfg.level = 10;
      cov.sample_data();

      coverage_pct = cov.get_cov();
      $display("After sample(mode=200,level=10): %0.2f%%", coverage_pct);

      // More samples to increase coverage
      cov.cfg.level = 5;
      cov.sample_data();
      cov.cfg.level = 14;
      cov.sample_data();

      coverage_pct = cov.get_cov();
      $display("Final coverage: %0.2f%%", coverage_pct);

      if (coverage_pct >= 50.0) begin
         $write("*-* All Finished *-*\n");
      end else begin
         $display("ERROR: Expected >= 50%%, got %0.2f%%", coverage_pct);
      end
      $finish;
   end
endmodule
