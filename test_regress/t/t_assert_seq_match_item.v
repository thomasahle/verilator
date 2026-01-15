// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026.
// SPDX-License-Identifier: CC0-1.0

// Test sequence match items parsing (IEEE 1800-2017 Section 16.10.1)
// Note: This tests that the syntax is accepted; match item side effects
// (assignments) are simplified to just the sequence expression.

module t;
   int a, b, x, y;

   // Sequence with single match item
   sequence s1;
      (a > 0, x = a) ##1 (b > 0);
   endsequence

   // Sequence with multiple match items
   sequence s2;
      (a > 0, x = a, y = b) ##1 (b > 0);
   endsequence

   // Sequence with match items and increment
   sequence s3;
      (a > 0, x++) ##1 (b > 0);
   endsequence

   // Nested sequence usage
   property p1;
      @(posedge a) s1;
   endproperty

   // Test compilation
   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
