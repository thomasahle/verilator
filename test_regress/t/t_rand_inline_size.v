// DESCRIPTION: Verilator: Test for inline array size constraints
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test the pattern used in SPI AVIP:
//   req.randomize() with { req.data.size() == 1; }
//
// This currently fails because size() in inline constraints is treated as state

/* verilator lint_off WIDTHTRUNC */

class packet;
   rand bit [7:0] data[];
   rand int value;

   // Class-level constraint works
   constraint c_default { data.size() inside {[1:4]}; }
endclass

module t;
   packet pkt;
   int ok;

   initial begin
      pkt = new;

      // Test 1: Class-level size constraint (should work)
      ok = pkt.randomize();
      if (!ok) $stop;
      if (pkt.data.size() < 1 || pkt.data.size() > 4) $stop;
      $display("Test 1 passed: class-level size constraint, size=%0d", pkt.data.size());

      // Test 2: Inline size constraint (currently fails)
      ok = pkt.randomize() with { data.size() == 2; };
      if (!ok) begin
         $display("Test 2 FAILED: inline size constraint");
         $stop;
      end
      if (pkt.data.size() != 2) begin
         $display("Test 2 FAILED: expected size 2, got %0d", pkt.data.size());
         $stop;
      end
      $display("Test 2 passed: inline size constraint, size=%0d", pkt.data.size());

      // Test 3: Inline constraint overriding class constraint
      ok = pkt.randomize() with { data.size() == 3; value == 42; };
      if (!ok) begin
         $display("Test 3 FAILED: inline size + value constraint");
         $stop;
      end
      if (pkt.data.size() != 3) begin
         $display("Test 3 FAILED: expected size 3, got %0d", pkt.data.size());
         $stop;
      end
      if (pkt.value != 42) begin
         $display("Test 3 FAILED: expected value 42, got %0d", pkt.value);
         $stop;
      end
      $display("Test 3 passed: inline size + value constraint");

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
