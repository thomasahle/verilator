// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test non-overlapping followed-by operators #-# and #=#
// These operators are similar to |-> and |=> but for sequence expressions

module t;

   logic clk = 0;
   always #5 clk = ~clk;

   int cyc = 0;
   logic req, ack, data_valid;

   // Create a sequence where req -> ack -> data_valid
   always @(posedge clk) begin
      cyc <= cyc + 1;
      case (cyc)
         0: begin req <= 1; ack <= 1; data_valid <= 0; end  // req and ack same cycle
         1: begin req <= 0; ack <= 0; data_valid <= 1; end  // data_valid next cycle
         2: begin req <= 0; ack <= 0; data_valid <= 0; end
         3: begin req <= 1; ack <= 1; data_valid <= 0; end  // Another sequence
         4: begin req <= 0; ack <= 0; data_valid <= 1; end
         5: begin req <= 0; ack <= 0; data_valid <= 0; end
         6: begin
            $write("*-* All Finished *-*\n");
            $finish;
         end
         default: ;
      endcase
   end

   // Test #-# (overlapped followed-by, like |->)
   // req #-# ack means: if req is true, then ack must be true at the same cycle
   // This is the same as req |-> ack
   ap_hash_minus: assert property (@(posedge clk)
      disable iff (cyc < 1)
      req #-# ack)
   else $error("ap_hash_minus failed at cyc=%0d, req=%0d, ack=%0d", cyc, req, ack);

   // Test #=# (non-overlapped followed-by, like |=>)
   // ack #=# data_valid means: if ack is true, then data_valid must be true next cycle
   // This is the same as ack |=> data_valid
   ap_hash_equal: assert property (@(posedge clk)
      disable iff (cyc < 1)
      ack #=# data_valid)
   else $error("ap_hash_equal failed at cyc=%0d, ack=%0d, data_valid=%0d", cyc, ack, data_valid);

endmodule
