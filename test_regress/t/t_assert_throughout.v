// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test for SVA throughout operator (IEEE 1800-2017 16.9.8)
// "a throughout seq" - expression a must hold at every clock during seq
// Simplified for Verilator: transforms to a && seq

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   int   cyc = 0;
   logic valid, ready;

   // Simple throughout test using implication:
   // When valid rises, valid must hold throughout (until we check ready)
   // This is the common AXI/AHB handshake pattern
   property p_valid_throughout_ready;
      @(posedge clk) disable iff (cyc < 3)
      // When both are true, pass. When ready is false, don't check.
      ready |-> (valid throughout ready);
   endproperty

   assert property (p_valid_throughout_ready)
      else $error("valid_throughout_ready failed at cyc=%0d", cyc);

   always @(posedge clk) begin
      cyc <= cyc + 1;

      // Test pattern: when ready is high, valid must also be high
      case (cyc)
         0: begin valid <= 0; ready <= 0; end
         1: begin valid <= 0; ready <= 0; end
         2: begin valid <= 0; ready <= 0; end  // Both low - ready low, no check
         3: begin valid <= 1; ready <= 0; end  // valid high, ready low - no check
         4: begin valid <= 1; ready <= 1; end  // Both high - valid throughout ready OK
         5: begin valid <= 0; ready <= 0; end  // Both low - no check
         6: begin valid <= 1; ready <= 1; end  // Both high - OK
         7: begin valid <= 1; ready <= 0; end  // ready low - no check
         8: begin valid <= 1; ready <= 1; end  // Both high - OK
         10: begin
            $write("*-* All Coverage Coverage *-*\n");
            $finish;
         end
         default: begin valid <= 0; ready <= 0; end
      endcase
   end

endmodule
