// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test for $past with explicit clock argument
// IEEE 1800-2017 Section 16.9.3

module t(/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   logic [7:0] counter = 0;
   logic [7:0] past_counter;
   logic [7:0] past_counter_2;

   // Counter increments each cycle
   always @(posedge clk) begin
      counter <= counter + 1;
   end

   // Test $past with explicit clock argument
   // $past(expr, num_cycles, expr2, clock)
   // expr2 (gating expression) is not yet supported, so we pass empty
   // The clock argument specifies which clock edge to sample on
   assign past_counter = $past(counter, 1, , @(posedge clk));
   assign past_counter_2 = $past(counter, 2, , @(posedge clk));

   int cyc = 0;
   always @(posedge clk) begin
      cyc <= cyc + 1;
      if (cyc > 3) begin
         // past_counter should be 1 behind counter value from previous cycle
         // Due to NBA, counter at cyc has already updated, so past should be counter from previous edge
         if (past_counter !== counter - 1) begin
            $display("past_counter=%0d counter=%0d diff=%0d", past_counter, counter, counter - past_counter);
         end
      end
      if (cyc == 10) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
