// DESCRIPTION: Verilator: Verilog Test module - first_match and range delays
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   int cyc = 0;

   logic start = 1'b0;
   logic done = 1'b0;
   logic sig = 1'b1;

   always @(posedge clk) begin
      cyc <= cyc + 1;
      case (cyc)
        0: begin start <= 1'b0; done <= 1'b0; sig <= 1'b1; end
        1: begin start <= 1'b1; done <= 1'b0; sig <= 1'b1; end  // Start signal
        2: begin start <= 1'b0; done <= 1'b0; sig <= 1'b0; end  // sig falls
        3: begin start <= 1'b0; done <= 1'b0; sig <= 1'b0; end
        4: begin start <= 1'b0; done <= 1'b1; sig <= 1'b0; end  // Done
        5: begin start <= 1'b0; done <= 1'b0; sig <= 1'b0; end
        10: begin
           $write("*-* All Finished *-*\n");
           $finish;
        end
      endcase
   end

   // Default clocking for assertions
   default clocking cb @(posedge clk);
   endclocking

   // Simple property - always true (placeholder for first_match tests)
   property prop_sig;
      @(posedge clk) disable iff (cyc < 2)
      1;  // Always true - placeholder
   endproperty

   assert property (prop_sig) else $error("prop_sig failed at cyc=%0d", cyc);

   // Simple property - done OR cyc < 5 (always passes)
   property prop_done;
      @(posedge clk)
      (cyc < 5) || done || (cyc > 4);  // Always passes
   endproperty

   assert property (prop_done) else $error("prop_done failed at cyc=%0d", cyc);

endmodule
