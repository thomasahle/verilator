// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test basic covergroup with explicit sample() calls

module t;
   int data;
   int mode;

   covergroup cg;
      // Coverpoint with explicit bins
      DATA_CP: coverpoint data {
         bins low = {[0:3]};
         bins mid = {[4:7]};
         bins high = {[8:15]};
      }

      // Mode coverpoint
      MODE_CP: coverpoint mode {
         bins off = {0};
         bins on = {1};
      }
   endgroup

   cg cg_inst;

   initial begin
      cg_inst = new;

      // Sample with low data
      data = 2;
      mode = 0;
      cg_inst.sample();

      // Sample with mid data
      data = 5;
      mode = 1;
      cg_inst.sample();

      // Sample with high data
      data = 10;
      mode = 0;
      cg_inst.sample();

      // Sample again with same data (should increase count)
      cg_inst.sample();

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
