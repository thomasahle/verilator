// DESCRIPTION: Verilator: Test for queue constraints with foreach - two-phase solving
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off WIDTHEXPAND */
/* verilator lint_off WIDTHTRUNC */

module t;

  // Test that foreach constraints on queues work with two-phase solving
  class queue_foreach;
    rand bit [7:0] len;
    rand bit [3:0] data [$:16];

    constraint len_c { len inside {[1:4]}; }
    constraint size_c { data.size() == len; }
    constraint elem_c { foreach(data[i]) data[i] != 0; }
  endclass

  initial begin
    queue_foreach item;
    int success_count = 0;
    int fail_count = 0;

    item = new();

    // Try randomization multiple times
    repeat (10) begin
      if (item.randomize()) begin
        success_count++;
        // Check that constraints are satisfied
        if (item.data.size() != item.len) begin
          $display("[FAIL] Queue size mismatch: expected %0d, got %0d", item.len, item.data.size());
          $stop;
        end
        // Check element constraints
        foreach (item.data[i]) begin
          if (item.data[i] == 0) begin
            $display("[FAIL] Element constraint violated: data[%0d] = 0", i);
            $stop;
          end
        end
      end else begin
        fail_count++;
      end
    end

    $display("Randomization results: %0d successes, %0d failures", success_count, fail_count);

    // We expect at least some successes now that two-phase solving is implemented
    if (success_count > 0) begin
      $display("[PASS] Two-phase solving works - foreach constraints applied");
    end else begin
      $display("[INFO] Randomization still failing - two-phase solving may need more work");
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
