// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test casex with matches (IEEE 1800-2017 12.6)

module t;
   typedef union tagged {
      void Invalid;
      bit [7:0] Valid;
   } MaybeInt;

   MaybeInt m;

   initial begin
      // Test casex with matches - basic functionality
      m = tagged Valid (8'd42);

      casex (m) matches
         tagged Invalid: begin
            $display("Got invalid");
            $stop;
         end
         tagged Valid .v: begin
            $display("Got valid: %d", v);
            if (v != 42) $stop;
         end
         default: begin
            $display("Got default");
            $stop;
         end
      endcase

      m = tagged Invalid;

      casex (m) matches
         tagged Invalid: begin
            $display("Got invalid");
         end
         tagged Valid .v: begin
            $display("Got valid: %d", v);
            $stop;
         end
      endcase

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
