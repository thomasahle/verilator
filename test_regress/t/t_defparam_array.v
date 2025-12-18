// DESCRIPTION: Verilator: Test defparam with array index in hierarchical path
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
   genvar i;
   generate
      for (i = 0; i < 2; i = i + 1) begin : gen_block
         sub_module inst ();
         // Use defparam with array index to override parameter
         defparam gen_block[i].inst.PARAM = i + 1;
      end
   endgenerate

   initial begin
      // Verify parameters were set correctly
      if (gen_block[0].inst.PARAM !== 1) begin
         $display("FAIL: gen_block[0].inst.PARAM = %0d, expected 1", gen_block[0].inst.PARAM);
         $stop;
      end
      if (gen_block[1].inst.PARAM !== 2) begin
         $display("FAIL: gen_block[1].inst.PARAM = %0d, expected 2", gen_block[1].inst.PARAM);
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
