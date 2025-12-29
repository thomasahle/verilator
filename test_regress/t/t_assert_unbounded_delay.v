// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test for SVA unbounded delay ##[min:$]

module t;
   logic clk = 0;
   always #5 clk = ~clk;

   int   cyc = 0;
   logic req, ack;

   // Unbounded delay: req eventually leads to ack (after 1+ cycles)
   property p_eventually_ack;
      @(posedge clk)
      $rose(req) |-> ##[1:$] ack;
   endproperty

   // Another unbounded delay pattern
   property p_req_then_ack;
      @(posedge clk)
      (req && !ack) |-> ##[1:$] ack;
   endproperty

   assert property (p_eventually_ack)
      else $error("p_eventually_ack failed at cyc=%0d", cyc);

   assert property (p_req_then_ack)
      else $error("p_req_then_ack failed at cyc=%0d", cyc);

   always @(posedge clk) begin
      cyc <= cyc + 1;

      case (cyc)
         0: begin req <= 0; ack <= 0; end
         1: begin req <= 0; ack <= 0; end
         // Test: req rises, ack comes after 2 cycles
         2: begin req <= 1; ack <= 0; end
         3: begin req <= 0; ack <= 0; end
         4: begin ack <= 1; end  // ack arrives
         5: begin req <= 0; ack <= 0; end
         // Test: req rises, ack comes immediately next cycle
         6: begin req <= 1; ack <= 0; end
         7: begin req <= 0; ack <= 1; end  // ack arrives
         8: begin ack <= 0; end
         10: begin
            $write("*-* All Finished *-*\n");
            $finish;
         end
         default: begin end
      endcase
   end

endmodule
