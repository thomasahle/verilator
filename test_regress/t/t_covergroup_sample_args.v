// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test covergroup sample() function arguments
// IEEE 1800-2017 19.8.1 - sample() with arguments

module t;
   // Transaction class
   class Transaction;
      bit [7:0] data;
      bit [1:0] addr;
   endclass

   // Covergroup with sample arguments
   covergroup cg with function sample(Transaction t);
      DATA_CP: coverpoint t.data {
         bins low = {[0:127]};
         bins high = {[128:255]};
      }
      ADDR_CP: coverpoint t.addr {
         bins a0 = {0};
         bins a1 = {1};
         bins a2 = {2};
         bins a3 = {3};
      }
   endgroup

   cg cg_inst;
   Transaction tr;
   real coverage_pct;

   initial begin
      cg_inst = new;
      tr = new;

      // Before sampling - 0%
      coverage_pct = cg_inst.get_inst_coverage();
      $display("Coverage before sampling: %0.2f%%", coverage_pct);

      // Sample with tr.data=50 (low), tr.addr=0
      tr.data = 50;
      tr.addr = 0;
      cg_inst.sample(tr);

      coverage_pct = cg_inst.get_inst_coverage();
      $display("After sample(data=50,addr=0): %0.2f%%", coverage_pct);
      // Expected: 2 of 6 bins = 33.33%

      // Sample with tr.data=200 (high), tr.addr=2
      tr.data = 200;
      tr.addr = 2;
      cg_inst.sample(tr);

      coverage_pct = cg_inst.get_inst_coverage();
      $display("After sample(data=200,addr=2): %0.2f%%", coverage_pct);
      // Expected: 4 of 6 bins = 66.67%

      // Sample with tr.addr=1 and tr.addr=3
      tr.addr = 1;
      cg_inst.sample(tr);
      tr.addr = 3;
      cg_inst.sample(tr);

      coverage_pct = cg_inst.get_inst_coverage();
      $display("After sampling all addrs: %0.2f%%", coverage_pct);
      // Expected: 6 of 6 bins = 100%

      if (coverage_pct >= 99.0) begin
         $write("*-* All Finished *-*\n");
      end else begin
         $display("ERROR: Expected ~100%%, got %0.2f%%", coverage_pct);
      end
      $finish;
   end
endmodule
