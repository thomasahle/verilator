// DESCRIPTION: Verilator: Test duplicate parameter connection (suppressed warning)
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test case: Using both inline parameter AND defparam for same parameter
// This pattern is used by some UVM testbenches (e.g., AXI4 AVIP)
// With -Wno-PINDUP, this should compile and run successfully

module t;
   genvar i;
   generate
      for (i = 0; i < 2; i = i + 1) begin : gen_block
         // Inline parameter connection
         sub_module #(.PARAM(i)) inst ();
         // defparam for same parameter (uses same value)
         defparam gen_block[i].inst.PARAM = i;
      end
   endgenerate

   initial begin
      // Verify parameters were set correctly (defparam should not override
      // since it has the same value as the inline parameter)
      if (gen_block[0].inst.PARAM !== 0) begin
         $display("FAIL: gen_block[0].inst.PARAM = %0d, expected 0", gen_block[0].inst.PARAM);
         $stop;
      end
      if (gen_block[1].inst.PARAM !== 1) begin
         $display("FAIL: gen_block[1].inst.PARAM = %0d, expected 1", gen_block[1].inst.PARAM);
         $stop;
      end
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
