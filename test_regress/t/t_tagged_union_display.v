// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test $display %p with tagged unions (IEEE 1800-2017 7.3.2)

module t;
   typedef union tagged {
      void Invalid;
      bit [7:0] Valid;
   } MaybeInt;

   MaybeInt m;

   initial begin
      m = tagged Valid (8'd42);
      $display("Valid case: %p", m);

      m = tagged Invalid;
      $display("Invalid case: %p", m);

      $write("*-* All Coverage Covered *-*\n");
      $finish;
   end
endmodule
