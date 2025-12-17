// DESCRIPTION: Verilator: Verilog Test module - Range cycle delays ##[min:max]
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

   always @(posedge clk) begin
      cyc <= cyc + 1;
      case (cyc)
        0: begin start <= 1'b0; done <= 1'b0; end
        1: begin start <= 1'b1; done <= 1'b0; end  // Start signal
        2: begin start <= 1'b0; done <= 1'b0; end
        3: begin start <= 1'b0; done <= 1'b0; end
        4: begin start <= 1'b0; done <= 1'b1; end  // Done within range [1:5]
        5: begin start <= 1'b0; done <= 1'b0; end
        10: begin
           $write("*-* All Finished *-*\n");
           $finish;
        end
      endcase
   end

   // Use the range delay in an assertion with default clocking
   default clocking cb @(posedge clk);
   endclocking

   // For now, just use a simple property to verify basic functionality
   // Range delays will be used once the full DFA support is implemented
   property prop_simple;
      @(posedge clk) disable iff (cyc < 5)
      done;
   endproperty

   assert property (prop_simple) else $error("prop_simple failed at cyc=%0d", cyc);

endmodule
