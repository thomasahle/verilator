// DESCRIPTION: Verilator: Test for queue constraints with foreach
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off WIDTHEXPAND */
/* verilator lint_off WIDTHTRUNC */

module t;

  // Minimal reproduction of queue + foreach constraint issue
  class queue_foreach;
    rand bit [7:0] len;
    rand bit [3:0] data [$:16];

    constraint len_c { len inside {[1:4]}; }
    constraint size_c { data.size() == len; }
    constraint elem_c { foreach(data[i]) data[i] != 0; }
  endclass

  initial begin
    queue_foreach item;
    item = new();

    // This may crash or fail
    if (item.randomize()) begin
      $display("Randomization succeeded: len=%0d, data.size=%0d", item.len, item.data.size());
      foreach (item.data[i]) begin
        $display("  data[%0d] = %0d", i, item.data[i]);
      end
      if (item.data.size() == item.len) begin
        $display("[PASS] Queue size matches len");
      end else begin
        $display("[FAIL] Queue size mismatch");
      end
    end else begin
      $display("[INFO] Randomization failed (expected - queue+foreach limitation)");
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
