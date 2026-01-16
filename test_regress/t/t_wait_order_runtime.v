// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test wait_order statement runtime behavior (IEEE 1800-2017 15.4)

module t;

   event e1, e2, e3;
   int in_order_count = 0;
   int out_of_order_count = 0;

   // Test 1: Events in correct order
   initial begin
      fork
         begin
            // Trigger events in order: e1, e2, e3
            #10 -> e1;
            #10 -> e2;
            #10 -> e3;
         end
         begin
            wait_order(e1, e2, e3)
               in_order_count++;
            else
               out_of_order_count++;
         end
      join
   end

   // Test 2: Events out of order (e2 before e1)
   event f1, f2, f3;
   initial begin
      fork
         begin
            // Trigger events out of order: f2, f1, f3
            #100 -> f2;  // Out of order!
            #10 -> f1;
            #10 -> f3;
         end
         begin
            wait_order(f1, f2, f3)
               in_order_count++;
            else
               out_of_order_count++;
         end
      join
   end

   // Test 3: Events out of order (e3 before e2)
   event g1, g2, g3;
   initial begin
      fork
         begin
            // Trigger events: g1 in order, then g3 before g2
            #200 -> g1;
            #10 -> g3;  // Out of order!
            #10 -> g2;
         end
         begin
            wait_order(g1, g2, g3)
               in_order_count++;
            else
               out_of_order_count++;
         end
      join
   end

   // Test 4: Two events only, in order
   event h1, h2;
   initial begin
      fork
         begin
            #300 -> h1;
            #10 -> h2;
         end
         begin
            wait_order(h1, h2)
               in_order_count++;
            else
               out_of_order_count++;
         end
      join
   end

   // Test 5: Single event (trivial case)
   event j1;
   initial begin
      fork
         begin
            #400 -> j1;
         end
         begin
            wait_order(j1)
               in_order_count++;
            else
               out_of_order_count++;
         end
      join
   end

   // Check results
   initial begin
      #500;
      $display("In order count: %0d (expected 3)", in_order_count);
      $display("Out of order count: %0d (expected 2)", out_of_order_count);
      if (in_order_count == 3 && out_of_order_count == 2) begin
         $write("*-* All Coverage Coverage Tests Passed *-*\n");
         $finish;
      end else begin
         $error("FAILED: Expected 3 in-order and 2 out-of-order");
         $stop;
      end
   end

endmodule
