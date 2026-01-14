// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/);
   // Tagged union with void and data members
   typedef union tagged {
      void Invalid;
      int Valid;
   } Maybe;

   // Tagged union with multiple data members
   typedef union tagged {
      void None;
      bit [7:0] Small;
      bit [31:0] Medium;
      bit [63:0] Large;
   } MultiSize;

   Maybe m;
   MultiSize ms;

   initial begin
      // Test basic member access
      m.Valid = 42;
      if (m.Valid != 42) $stop;

      ms.Small = 8'hAB;
      if (ms.Small != 8'hAB) $stop;

      ms.Medium = 32'h12345678;
      if (ms.Medium != 32'h12345678) $stop;

      ms.Large = 64'hDEADBEEFCAFEBABE;
      if (ms.Large != 64'hDEADBEEFCAFEBABE) $stop;

      // Test width calculation
      // Maybe: max(0,32) + ceil(log2(2)) = 32 + 1 = 33
      if ($bits(Maybe) != 33) $stop;

      // MultiSize: max(0,8,32,64) + ceil(log2(4)) = 64 + 2 = 66
      if ($bits(MultiSize) != 66) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
