// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024.
// SPDX-License-Identifier: CC0-1.0

// Test repeat event control as intra-assignment timing:
// IEEE 1800-2017 Section 9.4.5.1
// lvalue = repeat(n) @(event) expr;

module t;
   reg clk = 0;
   int value = 0;
   int result = 0;

   // Generate clock
   always #5 clk = ~clk;

   // Increment value on every posedge
   always @(posedge clk) value = value + 1;

   initial begin
      // Wait for initial setup
      @(posedge clk);

      // Test: Intra-assignment repeat event control
      // result = repeat(3) @(posedge clk) value;
      // This should wait for 3 posedges then assign value
      result = repeat(3) @(posedge clk) value;

      // After 3 more posedges, value should be 4 (1+3) and result should be 4
      if (result !== 4) begin
         $display("FAIL: result = %0d, expected 4", result);
         $stop;
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
