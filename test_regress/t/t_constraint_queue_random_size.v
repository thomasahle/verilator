// DESCRIPTION: Verilator: Test queue size constraint with random size variable
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off CONSTRAINTIGN */
/* verilator lint_off WIDTHEXPAND */
/* verilator lint_off WIDTHTRUNC */
class queue_random_size;
  rand bit [7:0] len;
  rand bit [7:0] data [$:256];

  // Size constraint uses another random variable
  constraint len_c { len inside {[1:4]}; }
  constraint size_c { data.size() == len; }

  function new();
  endfunction
endclass

module t;
  initial begin
    queue_random_size obj = new();
    int success;

    $display("Testing queue with random size variable...");

    success = obj.randomize();

    if (success) begin
      $display("Randomization succeeded: len=%0d, data.size=%0d", obj.len, obj.data.size());

      if (obj.data.size() == obj.len) begin
        $display("[PASS] Queue size matches random len");
      end else begin
        $display("[FAIL] Queue size (%0d) != len (%0d)", obj.data.size(), obj.len);
      end
    end else begin
      $display("[FAIL] Randomization failed");
    end

    $display("*-* All Finished *-*");
    $finish;
  end
endmodule
