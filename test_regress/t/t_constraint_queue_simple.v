// DESCRIPTION: Verilator: Test for simple queue size constraints
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

  // Minimal reproduction of queue + size constraint (no foreach)
  class queue_simple;
    rand bit [7:0] len;
    rand bit [3:0] data [$:16];

    constraint len_c { len inside {[1:4]}; }
    constraint size_c { data.size() == len; }
    // No foreach constraint
  endclass

  initial begin
    queue_simple item;
    item = new();

    // This should work
    if (item.randomize()) begin
      $display("Randomization succeeded: len=%0d, data.size=%0d", item.len, item.data.size());
      if (item.data.size() == item.len) begin
        $display("[PASS] Queue size matches len");
      end else begin
        $display("[FAIL] Queue size mismatch: expected %0d, got %0d", item.len, item.data.size());
      end
    end else begin
      $display("[FAIL] Randomization failed");
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
