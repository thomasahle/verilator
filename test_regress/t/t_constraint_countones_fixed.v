// DESCRIPTION: Verilator: Test for $countones in foreach on fixed array
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

  // Test class with fixed array (no queue size constraints)
  class fixed_array;
    rand bit [2:0] awsize;
    rand bit [3:0] wstrb [4];  // Fixed size array instead of queue

    // Restrict awsize to valid values (0=1byte, 1=2bytes, 2=4bytes)
    constraint awsize_c { awsize inside {[0:2]}; }

    // Each strobe must be non-zero
    constraint wstrb_nonzero_c { foreach(wstrb[i]) wstrb[i] != 0; }

    // The problematic constraint: $countones in foreach
    constraint wstrb_countones_c { foreach(wstrb[i]) $countones(wstrb[i]) == 2**awsize; }
  endclass

  int pass_count = 0;
  int fail_count = 0;

  initial begin
    fixed_array item;

    item = new();

    // Try randomizing
    if (item.randomize()) begin
      int all_correct = 1;
      int expected_ones = 2**item.awsize;

      $display("awsize=%0d, expected_ones=%0d", item.awsize, expected_ones);

      foreach (item.wstrb[i]) begin
        int ones = $countones(item.wstrb[i]);
        if (ones != expected_ones) begin
          $display("  [FAIL] wstrb[%0d]=%b has %0d ones, expected %0d",
                   i, item.wstrb[i], ones, expected_ones);
          all_correct = 0;
        end else begin
          $display("  [OK] wstrb[%0d]=%b has %0d ones", i, item.wstrb[i], ones);
        end
      end

      if (all_correct) begin
        $display("[PASS] All constraints satisfied");
        pass_count++;
      end else begin
        $display("[FAIL] Some constraints not satisfied");
        fail_count++;
      end
    end else begin
      $display("[INFO] Randomization failed");
      fail_count++;
    end

    $display("Test complete: %0d passed, %0d failed", pass_count, fail_count);
    if (fail_count == 0) begin
      $write("*-* All Finished *-*\n");
    end
    $finish;
  end

endmodule
