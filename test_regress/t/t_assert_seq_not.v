// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test for SVA boolean negation (!) in sequence expressions

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   int   cyc = 0;
   logic a, b, stable_sig;
   logic prev_stable;

   // Boolean negation in sequence: check !$stable() pattern
   property p_not_stable;
      @(posedge clk)
      a |-> ##1 !$stable(stable_sig);
   endproperty

   // Negation combined with other expressions
   property p_not_and;
      @(posedge clk)
      (a && !b) |-> ##1 $stable(stable_sig);
   endproperty

   // Simple negation
   property p_simple_not;
      @(posedge clk)
      a |-> !b;
   endproperty

   assert property (p_not_stable)
      else $error("p_not_stable failed at cyc=%0d", cyc);

   assert property (p_not_and)
      else $error("p_not_and failed at cyc=%0d", cyc);

   assert property (p_simple_not)
      else $error("p_simple_not failed at cyc=%0d", cyc);

   always @(posedge clk) begin
      cyc <= cyc + 1;
      prev_stable <= stable_sig;

      case (cyc)
         0: begin a <= 0; b <= 0; stable_sig <= 0; end
         1: begin a <= 0; b <= 0; stable_sig <= 0; end
         // Test !$stable: a triggers, stable_sig changes
         2: begin a <= 1; b <= 0; stable_sig <= 0; end
         3: begin a <= 0; b <= 0; stable_sig <= 1; end  // changed - !$stable is true
         4: begin stable_sig <= 1; end
         // Test !b: a true, b false
         5: begin a <= 1; b <= 0; end
         6: begin a <= 0; b <= 0; end
         // Test a && !b with stable
         7: begin a <= 1; b <= 0; stable_sig <= 1; end
         8: begin a <= 0; stable_sig <= 1; end  // stable_sig stable
         10: begin
            $write("*-* All Finished *-*\n");
            $finish;
         end
         default: begin end
      endcase
   end

endmodule
