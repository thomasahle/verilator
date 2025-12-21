// DESCRIPTION: Verilator: Test queue size + foreach with $countones
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off CONSTRAINTIGN */
/* verilator lint_off WIDTHEXPAND */
/* verilator lint_off WIDTHTRUNC */

class queue_test;
  rand bit [7:0] len;
  rand bit [2:0] size_val;
  rand bit [7:0] data [$:256];

  constraint len_c { len inside {[1:4]}; }
  constraint size_c { size_val inside {[0:2]}; }

  // Size constraint
  constraint data_size_c { data.size() == len; }

  // Foreach with $countones - similar to axi4_master_tx
  constraint elem_c { foreach(data[i]) $countones(data[i]) == 2**size_val; }

  function new();
  endfunction
endclass

module t;
  initial begin
    queue_test obj = new();
    int success;

    $display("Testing queue with $countones in foreach...");

    success = obj.randomize();

    if (success) begin
      $display("Randomization succeeded: len=%0d, size_val=%0d, data.size=%0d",
               obj.len, obj.size_val, obj.data.size());

      if (obj.data.size() == obj.len) begin
        $display("[PASS] Queue size matches len");
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
