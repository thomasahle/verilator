// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test basic covergroup parsing - syntax check only

class TestCov;
   int data;

   covergroup cg;
      // Coverpoint with explicit bins
      DATA_CP: coverpoint data {
         bins low = {[0:7]};
         bins high = {[8:15]};
      }
   endgroup

   function new();
      cg = new;
   endfunction
endclass

module t;
   TestCov tc;

   initial begin
      tc = new;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
