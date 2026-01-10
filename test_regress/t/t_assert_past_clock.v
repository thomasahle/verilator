// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test $past with clock argument (IEEE 1800-2017 16.9.3)
// Just verify the syntax is accepted

module t (/*AUTOARG*/
      clk
   );
   input clk;
   int cyc = 0;
   logic [7:0] val = 0;

   always @(posedge clk) begin
      cyc <= cyc + 1;
      val <= val + 8'd1;
      $display("t=%0t   cyc=%0d   val=%0d", $time, cyc, val);
      if (cyc == 10) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

   // Test $past with explicit clock argument
   // $past(expression, number_of_ticks, expression2, clocking_event)
   // We test with clocking_event = @(posedge clk)
   always @(posedge clk) begin
      if (cyc > 2) begin
         // $past with explicit clock - check value from 1 cycle ago
         if ($past(val, 1, , @(posedge clk)) != val - 8'd1) begin
            $display("$past with clock mismatch at cyc=%0d", cyc);
            $stop;
         end
      end
   end
endmodule
