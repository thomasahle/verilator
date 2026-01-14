// DESCRIPTION: Verilator: Verilog Test module
//
// Test reduction operations in constraints: |, &, $onehot, $onehot0
// These now have SMT support for constraint solving
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

   class WithReduction;
      rand bit [7:0] value;

      // Constraint using reduction OR: at least one bit set
      constraint has_bits { |value; }
   endclass

   class WithRedAnd;
      rand bit [3:0] value;

      // Constraint using reduction AND: all bits set
      constraint all_ones { &value; }
   endclass

   class WithOneHot;
      rand bit [7:0] value;

      // Constraint using $onehot: exactly one bit set
      constraint one_bit { $onehot(value); }
   endclass

   class WithOneHot0;
      rand bit [7:0] value;

      // Constraint using $onehot0: at most one bit set (includes zero)
      constraint at_most_one { $onehot0(value); }
   endclass

   int pass_count;
   int fail_count;

   initial begin
      WithReduction r;
      WithRedAnd a;
      WithOneHot oh;
      WithOneHot0 oh0;
      int success;
      int i;

      pass_count = 0;
      fail_count = 0;

      // Test 1: Reduction OR constraint
      $display("=== Test 1: Reduction OR (|value) ===");
      r = new();
      for (i = 0; i < 10; i++) begin
         success = r.randomize();
         if (!success) begin
            $display("FAIL: randomize failed");
            fail_count++;
         end else if (r.value == 0) begin
            $display("FAIL: value is 0 but should have at least one bit set");
            fail_count++;
         end else begin
            pass_count++;
         end
      end

      // Test 2: Reduction AND constraint
      $display("=== Test 2: Reduction AND (&value) ===");
      a = new();
      for (i = 0; i < 10; i++) begin
         success = a.randomize();
         if (!success) begin
            $display("FAIL: randomize failed");
            fail_count++;
         end else if (a.value != 4'hF) begin
            $display("FAIL: value is %h but should be all ones (0xF)", a.value);
            fail_count++;
         end else begin
            pass_count++;
         end
      end

      // Test 3: OneHot constraint
      $display("=== Test 3: $onehot(value) ===");
      oh = new();
      for (i = 0; i < 10; i++) begin
         success = oh.randomize();
         if (!success) begin
            $display("FAIL: randomize failed");
            fail_count++;
         end else if (!$onehot(oh.value)) begin
            $display("FAIL: value %h is not onehot", oh.value);
            fail_count++;
         end else begin
            pass_count++;
         end
      end

      // Test 4: OneHot0 constraint
      $display("=== Test 4: $onehot0(value) ===");
      oh0 = new();
      for (i = 0; i < 10; i++) begin
         success = oh0.randomize();
         if (!success) begin
            $display("FAIL: randomize failed");
            fail_count++;
         end else if (!$onehot0(oh0.value)) begin
            $display("FAIL: value %h is not onehot0", oh0.value);
            fail_count++;
         end else begin
            pass_count++;
         end
      end

      $display("\n=== Results: %0d passed, %0d failed ===", pass_count, fail_count);

      if (fail_count == 0) begin
         $write("*-* All Finished *-*\n");
      end else begin
         $stop;
      end
      $finish;
   end
endmodule
