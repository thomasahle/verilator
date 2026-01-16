// DESCRIPTION: Verilator: Test matches operator with variable binding
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026.
// SPDX-License-Identifier: CC0-1.0

// Test for matches with variable binding (IEEE 1800-2017 11.9.1)

// verilator lint_off WIDTHEXPAND

module t;

   typedef union tagged {
      void Invalid;
      int  Valid;
   } MaybeInt;

   typedef union tagged {
      void  Nothing;
      int   JustInt;
      logic [7:0] JustByte;
   } MaybeValue;

   MaybeInt mi;
   MaybeValue mv;
   int result;

   initial begin
      // Test binding with MaybeInt - tag only (no binding)
      mi = tagged Valid(42);
      if (mi matches tagged Valid) begin
         result = 1;  // Tag matched
      end else begin
         result = 0;
      end
      if (result !== 1) $stop;

      // Test binding with MaybeInt - bind value to variable
      mi = tagged Valid(42);
      if (mi matches tagged Valid .v) begin
         result = v;  // Should be 42
      end else begin
         result = 0;
      end
      if (result !== 42) $stop;

      // Test binding with different value
      mi = tagged Valid(100);
      if (mi matches tagged Valid .x) begin
         result = x;  // Should be 100
      end else begin
         result = 0;
      end
      if (result !== 100) $stop;

      // Test binding doesn't occur when tag doesn't match
      mi = tagged Invalid;
      result = 999;
      if (mi matches tagged Valid .y) begin
         result = y;  // Should NOT execute
      end
      if (result !== 999) $stop;  // Should still be 999

      // Test binding with MaybeValue
      mv = tagged JustByte(8'hAB);
      if (mv matches tagged JustByte .b) begin
         result = b;  // Should be 0xAB
      end else begin
         result = 0;
      end
      if (result !== 8'hAB) $stop;

      // Test wildcard pattern - doesn't bind, just matches
      mi = tagged Valid(123);
      if (mi matches tagged Valid .*) begin
         result = 1;  // Matches any value
      end else begin
         result = 0;
      end
      if (result !== 1) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
