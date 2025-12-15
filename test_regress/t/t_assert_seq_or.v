// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test for SVA sequence or/and operators

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   int   cyc = 0;
   logic a, b, c;

   // Sequence or: either a or b is true
   property p_seq_or;
      @(posedge clk)
      c |-> ##[0:2] (a or b);
   endproperty

   // Sequence and: both a and b are true
   property p_seq_and;
      @(posedge clk)
      c |-> ##[0:2] (a and b);
   endproperty

   assert property (p_seq_or)
      else $error("p_seq_or failed at cyc=%0d", cyc);

   assert property (p_seq_and)
      else $error("p_seq_and failed at cyc=%0d", cyc);

   always @(posedge clk) begin
      cyc <= cyc + 1;

      case (cyc)
         0: begin a <= 0; b <= 0; c <= 0; end
         1: begin a <= 0; b <= 0; c <= 0; end
         // Test or: c triggers, then a or b should be true
         2: begin c <= 1; a <= 0; b <= 0; end
         3: begin c <= 0; a <= 1; b <= 0; end  // a true - or satisfied
         4: begin a <= 0; b <= 0; end
         // Test and: c triggers, then a and b should be true
         5: begin c <= 1; a <= 0; b <= 0; end
         6: begin c <= 0; a <= 1; b <= 1; end  // both true - and satisfied
         7: begin a <= 0; b <= 0; end
         // Test or with b true
         8: begin c <= 1; a <= 0; b <= 0; end
         9: begin c <= 0; a <= 0; b <= 1; end  // b true - or satisfied
         10: begin a <= 0; b <= 0; end
         12: begin
            $write("*-* All Finished *-*\n");
            $finish;
         end
         default: begin end
      endcase
   end

endmodule
