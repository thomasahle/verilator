// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026.
// SPDX-License-Identifier: CC0-1.0

// Test for case...matches pattern matching (IEEE 1800-2017 12.5.4)

// verilator lint_off WIDTHCONCAT

module t;

   // Define tagged union types
   typedef union tagged {
      void Invalid;
      int  Valid;
   } MaybeInt;

   typedef union tagged {
      void  Nothing;
      int   JustInt;
      logic [31:0] JustLogic;
   } MaybeValue;

   MaybeInt mi;
   MaybeValue mv;
   int result;

   initial begin
      // Test case...matches with MaybeInt
      mi = tagged Invalid;
      case (mi) matches
         tagged Invalid: result = 0;
         tagged Valid: result = 1;
         default: result = -1;
      endcase
      if (result !== 0) $stop;

      mi = tagged Valid(42);
      case (mi) matches
         tagged Invalid: result = 0;
         tagged Valid: result = 1;
         default: result = -1;
      endcase
      if (result !== 1) $stop;

      // Test case...matches with MaybeValue
      mv = tagged Nothing;
      case (mv) matches
         tagged Nothing: result = 0;
         tagged JustInt: result = 1;
         tagged JustLogic: result = 2;
         default: result = -1;
      endcase
      if (result !== 0) $stop;

      mv = tagged JustInt(100);
      case (mv) matches
         tagged Nothing: result = 0;
         tagged JustInt: result = 1;
         tagged JustLogic: result = 2;
         default: result = -1;
      endcase
      if (result !== 1) $stop;

      mv = tagged JustLogic(32'hDEADBEEF);
      case (mv) matches
         tagged Nothing: result = 0;
         tagged JustInt: result = 1;
         tagged JustLogic: result = 2;
         default: result = -1;
      endcase
      if (result !== 2) $stop;

      // Test that default works when no pattern matches
      // (This can't actually happen with proper patterns, but test the flow)

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
