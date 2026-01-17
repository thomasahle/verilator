// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test tagged unions with struct members (IEEE 1800-2017 7.3.2)
// These anonymous structs need proper C++ struct emission for VL_TO_STRING.

module t;
   typedef union tagged {
      void Invalid;
      bit [7:0] Valid;
   } MaybeInt;

   MaybeInt m;

   initial begin
      m = tagged Valid (8'd42);
      case (m) matches
         tagged Invalid: $stop;
         tagged Valid .v: begin
            if (v != 42) $stop;
         end
      endcase

      m = tagged Invalid;
      case (m) matches
         tagged Invalid: begin
            $write("Got invalid\n");
         end
         tagged Valid .v: $stop;
      endcase

      $write("*-* All Coverage Covered *-*\n");
      $finish;
   end
endmodule
