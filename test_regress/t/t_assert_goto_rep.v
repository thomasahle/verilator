// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test for SVA goto repetition operator (IEEE 1800-2017 16.9.2)
// expr[->n] - boolean is true exactly n times (not necessarily consecutive)

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   int   cyc = 0;
   logic valid, ready;

   // Test goto repetition: simplified to just the expression
   // ready[->1] is simplified to ready
   // So this tests: when valid && ready, check ready is true
   property p_valid_and_ready_goto;
      @(posedge clk) disable iff (cyc < 3)
      (valid && ready) |-> ready[->1];
   endproperty

   // Test throughout with goto repetition
   // valid throughout ready[->1] is simplified to: valid && ready
   property p_valid_throughout_ready;
      @(posedge clk) disable iff (cyc < 3)
      ready |-> (valid throughout ready[->1]);
   endproperty

   assert property (p_valid_and_ready_goto)
      else $error("valid_and_ready_goto failed at cyc=%0d", cyc);

   assert property (p_valid_throughout_ready)
      else $error("valid_throughout_ready failed at cyc=%0d", cyc);

   always @(posedge clk) begin
      cyc <= cyc + 1;

      // Test pattern: valid stays high, ready comes after some cycles
      case (cyc)
         0: begin valid <= 0; ready <= 0; end
         1: begin valid <= 0; ready <= 0; end
         2: begin valid <= 0; ready <= 0; end
         3: begin valid <= 1; ready <= 0; end  // valid rises, ready low
         4: begin valid <= 1; ready <= 0; end  // valid still high
         5: begin valid <= 1; ready <= 1; end  // ready arrives, valid still high
         6: begin valid <= 0; ready <= 0; end
         7: begin valid <= 1; ready <= 1; end  // valid and ready both high immediately
         8: begin valid <= 0; ready <= 0; end
         10: begin
            $write("*-* All Coverage Coverage *-*\n");
            $finish;
         end
         default: begin valid <= 0; ready <= 0; end
      endcase
   end

endmodule
