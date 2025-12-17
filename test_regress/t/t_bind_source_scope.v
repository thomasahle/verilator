// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Thomas Ahle.
// SPDX-License-Identifier: CC0-1.0

// Test IEEE 1800-2017 Section 23.11: bind statement expressions resolved
// in the scope where the bind construct appears (source scope)

bit test_finished;

module checker_mod(input logic [31:0] data);
   // Check that data is connected properly
   initial begin
      test_finished = 1'b1;
   end
endmodule

module target_mod();
   // Target module has no ports - src_data is not visible here
endmodule

module source_mod();
   // src_data is in source_mod scope, not target_mod scope
   logic [31:0] src_data = 32'h12345678;

   target_mod target();

   // IEEE 1800-2017 23.11: The expression src_data should be resolved
   // in source_mod scope, even though the bind creates an instance
   // inside target_mod
   bind target_mod checker_mod check_inst(.data(src_data));
endmodule

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   source_mod src();

   always @(posedge clk) begin
      if (!test_finished) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
