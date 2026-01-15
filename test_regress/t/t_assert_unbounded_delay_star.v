// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026.
// SPDX-License-Identifier: CC0-1.0

// Test for SVA unbounded delay abbreviation ##[*]
// ##[*] is equivalent to ##[0:$] (zero or more cycles)

module t;
   logic clk = 0;
   always #5 clk = ~clk;

   int   cyc = 0;
   logic req, ack;

   // ##[*] means zero or more cycles - can be satisfied immediately
   property p_zero_or_more;
      @(posedge clk)
      req |-> ##[*] ack;
   endproperty

   // Test immediate satisfaction - req and ack both high
   property p_immediate;
      @(posedge clk)
      (req && ack) |-> ##[*] ack;
   endproperty

   assert property (p_zero_or_more)
      else $error("p_zero_or_more failed at cyc=%0d", cyc);

   assert property (p_immediate)
      else $error("p_immediate failed at cyc=%0d", cyc);

   always @(posedge clk) begin
      cyc <= cyc + 1;

      case (cyc)
         0: begin req <= 0; ack <= 0; end
         1: begin req <= 0; ack <= 0; end
         // Test: req and ack both high - should satisfy immediately (##[0:$])
         2: begin req <= 1; ack <= 1; end
         3: begin req <= 0; ack <= 0; end
         // Test: req high, ack comes after 2 cycles
         4: begin req <= 1; ack <= 0; end
         5: begin req <= 0; ack <= 0; end
         6: begin ack <= 1; end
         7: begin ack <= 0; end
         8: begin
            $write("*-* All Finished *-*\n");
            $finish;
         end
         default: begin end
      endcase
   end

endmodule
