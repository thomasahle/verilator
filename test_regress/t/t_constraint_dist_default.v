// DESCRIPTION: Verilator: dist default item
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class C;
   rand int x;
   constraint c_default { x dist { [0:3] := 1, default :/ 2 }; }
endclass

module t;
   initial begin
      C c = new;
      void'(c.randomize());
      $finish;
   end
endmodule
