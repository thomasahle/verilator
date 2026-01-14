// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test &&& level-sensitive event control (IEEE 1800-2017 9.4.2.1)

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   int   count = 0;
   logic enable = 0;
   bit   triggered = 0;

   // Generate enable signal
   always @(posedge clk) begin
      count <= count + 1;
      enable <= (count >= 3 && count < 7);
   end

   // Test &&& with posedge
   initial begin
      triggered = 0;
      // Wait for posedge clk when enable is high
      @(posedge clk &&& enable);
      triggered = 1;
      if (count < 4) begin
         $display("%%Error: Triggered too early at count=%0d", count);
         $stop;
      end
      $display("posedge clk &&& enable triggered at count=%0d", count);
   end

   // Test &&& with negedge
   logic nclk;
   assign nclk = ~clk;
   bit   neg_triggered = 0;

   initial begin
      neg_triggered = 0;
      // Wait a bit first
      repeat(5) @(posedge clk);
      // Now wait for negedge when enable is high
      @(negedge clk &&& enable);
      neg_triggered = 1;
      $display("negedge clk &&& enable triggered at count=%0d", count);
   end

   // Test &&& with change (level-sensitive)
   logic data = 0;
   bit   data_triggered = 0;

   always @(posedge clk) begin
      if (count == 5) data <= 1;
      if (count == 8) data <= 0;
   end

   initial begin
      data_triggered = 0;
      @(data &&& enable);
      data_triggered = 1;
      $display("data &&& enable triggered at count=%0d", count);
   end

   // Check all tests completed
   initial begin
      repeat(12) @(posedge clk);
      if (triggered && neg_triggered && data_triggered) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end else begin
         $display("%%Error: triggered=%0d neg_triggered=%0d data_triggered=%0d",
                  triggered, neg_triggered, data_triggered);
         $stop;
      end
   end

endmodule
