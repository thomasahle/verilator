// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026.
// SPDX-License-Identifier: CC0-1.0

// Test for tagged union expressions (IEEE 1800-2017 11.9)

module t;

   // Define a tagged union type
   typedef union tagged {
      void Invalid;
      int  Valid;
   } MaybeInt;

   // Define another tagged union with multiple members
   typedef union tagged {
      void  Nothing;
      int   JustInt;
      logic [31:0] JustLogic;
   } MaybeValue;

   MaybeInt mi;
   MaybeValue mv;

   initial begin
      // Create tagged union values with the 'tagged' expression
      // Test both with and without parentheses for void members
      mi = tagged Invalid;        // Void member - no parens (IEEE syntax)
      mi = tagged Invalid();      // Void member - with parens (also valid)
      mi = tagged Valid(42);      // Int member

      mv = tagged Nothing;        // Void member - no parens
      mv = tagged Nothing();      // Void member - with parens
      mv = tagged JustInt(100);   // Int member
      mv = tagged JustLogic(32'hDEADBEEF);  // Logic member

      // TODO: Tagged expressions in comparisons need type inference from LHS
      // For now just test assignments

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
