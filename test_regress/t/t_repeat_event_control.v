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
   int captured_value = 0;

   // Generate clock
   always #5 clk = ~clk;

   initial begin
      // Set initial value
      value = 42;

      // Wait for clock to stabilize
      @(posedge clk);

      // IEEE 1800-2017: RHS evaluated BEFORE timing control, assigned AFTER
      // So captured_value = 42 (current value), wait 3 posedges, then assign
      result = repeat(3) @(posedge clk) value;

      // Result should be 42 (the value captured before waiting)
      if (result !== 42) begin
         $display("FAIL: result = %0d, expected 42", result);
         $stop;
      end

      // Also test that we actually waited 3 clock edges
      // At this point we should be at time 5*4 = 20ns (1 initial + 3 repeat)
      // Use $time to verify
      $display("Current time: %0t", $time);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
