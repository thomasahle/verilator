// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test wait_order statement (IEEE 1800-2017 15.4)
// This tests that wait_order parses correctly and gives unsupported warning

module t;

   event e1, e2, e3;

   initial begin
      wait_order(e1, e2, e3)
         $display("in order");
      else
         $display("out of order");
   end

endmodule
