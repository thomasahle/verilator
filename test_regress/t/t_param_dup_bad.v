// DESCRIPTION: Verilator: Test duplicate parameter connection warning
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test case: Using both inline parameter AND defparam for same parameter
// This pattern is used by some UVM testbenches

module t;
   genvar i;
   generate
      for (i = 0; i < 2; i = i + 1) begin : gen_block
         // Inline parameter connection
         sub_module #(.PARAM(i)) inst ();
         // defparam for same parameter (duplicate connection)
         defparam gen_block[i].inst.PARAM = i;
      end
   endgenerate

   initial begin
      $display("*-* All Finished *-*");
      $finish;
   end
endmodule

module sub_module;
   parameter PARAM = 0;
   initial begin
      $display("sub_module instantiated with PARAM=%0d", PARAM);
   end
endmodule
