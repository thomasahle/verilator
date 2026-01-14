// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test repeat event control

module t;
   reg clk = 0;

   // Generate clock
   initial forever #5 clk = ~clk;

   // Test body
   initial begin
      int wait_count = 0;

      // Wait for 5 clock posedges (time 5, 15, 25, 35, 45)
      repeat (5) @(posedge clk);
      if ($time != 45) begin
         $display("ERROR: After repeat(5), time=%0d, expected=45", $time);
         $stop;
      end
      $display("After repeat(5) @(posedge clk): time=%0d (expected 45)", $time);

      // Wait for 3 more posedges (time 55, 65, 75)
      repeat (3) @(posedge clk);
      if ($time != 75) begin
         $display("ERROR: After repeat(3), time=%0d, expected=75", $time);
         $stop;
      end
      $display("After repeat(3) @(posedge clk): time=%0d (expected 75)", $time);

      // Wait for 0 clock cycles (should not wait)
      repeat (0) @(posedge clk);
      if ($time != 75) begin
         $display("ERROR: After repeat(0), time=%0d, expected=75", $time);
         $stop;
      end
      $display("After repeat(0) @(posedge clk): time=%0d (expected 75 - unchanged)", $time);

      // Wait for 1 clock cycle (time 85)
      repeat (1) @(posedge clk);
      if ($time != 85) begin
         $display("ERROR: After repeat(1), time=%0d, expected=85", $time);
         $stop;
      end
      $display("After repeat(1) @(posedge clk): time=%0d (expected 85)", $time);

      $write("*-* All Finished *-*\n");
      $finish;
   end

   // Timeout
   initial #200 begin
      $display("Timeout!");
      $stop;
   end

endmodule
