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
      // MaybeInt: 1 tag bit (2 members) + 32 data bits = 33 bits
      // tag=0 (Invalid), data=0 -> 33'h0_00000000
      if (mi !== 33'h0_00000000) $stop;

      mi = tagged Invalid();      // Void member - with parens (also valid)
      if (mi !== 33'h0_00000000) $stop;

      mi = tagged Valid(42);      // Int member
      // tag=1 (Valid), data=42 -> 33'h1_0000002A
      if (mi !== 33'h1_0000002A) $stop;

      mv = tagged Nothing;        // Void member - no parens
      // MaybeValue: 2 tag bits (3 members) + 32 data bits = 34 bits
      // tag=0 (Nothing), data=0 -> 34'h0_00000000
      if (mv !== 34'h0_00000000) $stop;

      mv = tagged Nothing();      // Void member - with parens
      if (mv !== 34'h0_00000000) $stop;

      mv = tagged JustInt(100);   // Int member
      // tag=1 (JustInt), data=100 -> 34'h1_00000064
      if (mv !== 34'h1_00000064) $stop;

      mv = tagged JustLogic(32'hDEADBEEF);  // Logic member
      // tag=2 (JustLogic), data=DEADBEEF -> 34'h2_DEADBEEF
      if (mv !== 34'h2_DEADBEEF) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
