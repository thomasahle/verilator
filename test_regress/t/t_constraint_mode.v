// DESCRIPTION: Verilator: Test constraint_mode functionality
// Tests enabling/disabling individual constraints at runtime
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class packet;
   rand bit [7:0] data;
   rand bit [3:0] addr;

   // Constraint 1: data must be > 100
   constraint data_high_c {
      data > 100;
   }

   // Constraint 2: data must be < 50
   constraint data_low_c {
      data < 50;
   }

   // Constraint 3: addr must be even
   constraint addr_even_c {
      addr[0] == 0;
   }

   function new();
   endfunction
endclass

module t;
   initial begin
      packet pkt;
      int high_count, low_count;
      int even_count, odd_count;
      int pass_count = 0;
      int test_count = 0;

      pkt = new();

      // Test 1: Default state - both constraints active (should fail to solve)
      // Since data_high_c and data_low_c conflict, disable one
      $display("Test 1: Disable conflicting constraint");
      test_count++;

      // Disable data_low_c, keep data_high_c
      pkt.data_low_c.constraint_mode(0);

      high_count = 0;
      for (int i = 0; i < 20; i++) begin
         if (pkt.randomize()) begin
            if (pkt.data > 100) high_count++;
         end
      end

      if (high_count == 20) begin
         $display("  PASS: All data values > 100 with data_high_c active");
         pass_count++;
      end else begin
         $display("  FAIL: Only %0d/20 values > 100", high_count);
      end

      // Test 2: Swap constraints - enable data_low_c, disable data_high_c
      $display("Test 2: Swap active constraint");
      test_count++;

      pkt.data_high_c.constraint_mode(0);
      pkt.data_low_c.constraint_mode(1);

      low_count = 0;
      for (int i = 0; i < 20; i++) begin
         if (pkt.randomize()) begin
            if (pkt.data < 50) low_count++;
         end
      end

      if (low_count == 20) begin
         $display("  PASS: All data values < 50 with data_low_c active");
         pass_count++;
      end else begin
         $display("  FAIL: Only %0d/20 values < 50", low_count);
      end

      // Test 3: Check constraint_mode() returns correct state
      $display("Test 3: Query constraint_mode state");
      test_count++;

      if (pkt.data_high_c.constraint_mode() == 0 &&
          pkt.data_low_c.constraint_mode() == 1) begin
         $display("  PASS: constraint_mode() returns correct states");
         pass_count++;
      end else begin
         $display("  FAIL: constraint_mode() returned wrong states");
         $display("        data_high_c=%0d (expected 0)", pkt.data_high_c.constraint_mode());
         $display("        data_low_c=%0d (expected 1)", pkt.data_low_c.constraint_mode());
      end

      // Test 4: Re-enable all constraints and use inline constraint
      $display("Test 4: Disable both, use inline constraint");
      test_count++;

      pkt.data_high_c.constraint_mode(0);
      pkt.data_low_c.constraint_mode(0);

      high_count = 0;
      low_count = 0;
      for (int i = 0; i < 20; i++) begin
         // Use inline constraint when base constraints are disabled
         if (pkt.randomize() with { data inside {[70:80]}; }) begin
            if (pkt.data >= 70 && pkt.data <= 80) begin
               high_count++;
            end
         end
      end

      if (high_count == 20) begin
         $display("  PASS: Inline constraint works when base constraints disabled");
         pass_count++;
      end else begin
         $display("  FAIL: Only %0d/20 values in range [70:80]", high_count);
      end

      // Test 5: addr_even_c constraint
      $display("Test 5: Test addr_even_c constraint");
      test_count++;

      // Re-enable data_high_c for this test
      pkt.data_high_c.constraint_mode(1);
      pkt.data_low_c.constraint_mode(0);

      even_count = 0;
      for (int i = 0; i < 20; i++) begin
         if (pkt.randomize()) begin
            if (pkt.addr[0] == 0) even_count++;
         end
      end

      if (even_count == 20) begin
         $display("  PASS: All addr values are even");
         pass_count++;
      end else begin
         $display("  FAIL: Only %0d/20 addr values even", even_count);
      end

      // Test 6: Disable addr_even_c
      $display("Test 6: Disable addr_even_c");
      test_count++;

      pkt.addr_even_c.constraint_mode(0);

      even_count = 0;
      odd_count = 0;
      for (int i = 0; i < 100; i++) begin
         if (pkt.randomize()) begin
            if (pkt.addr[0] == 0) even_count++;
            else odd_count++;
         end
      end

      // With constraint disabled, should see both even and odd addresses
      if (even_count > 0 && odd_count > 0) begin
         $display("  PASS: Got both even (%0d) and odd (%0d) addresses", even_count, odd_count);
         pass_count++;
      end else begin
         $display("  FAIL: even=%0d, odd=%0d (expected both > 0)", even_count, odd_count);
      end

      // Summary
      $display("");
      $display("Results: %0d/%0d tests passed", pass_count, test_count);

      if (pass_count == test_count) begin
         $display("*-* All Finished *-*");
      end else begin
         $display("FAIL: Some tests failed");
         $stop;
      end
      $finish;
   end
endmodule
