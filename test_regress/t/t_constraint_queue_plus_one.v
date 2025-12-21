// DESCRIPTION: Verilator: Test queue size == len + 1
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off CONSTRAINTIGN */
/* verilator lint_off WIDTHEXPAND */
/* verilator lint_off WIDTHTRUNC */
class queue_test;
  rand bit [7:0] awlen;
  rand bit [7:0] wdata [$:256];
  rand bit [3:0] wstrb [$:256];

  constraint len_c { awlen inside {[0:3]}; }

  // This is exactly the axi4 pattern: size == awlen + 1
  constraint wdata_c1 { wdata.size() == awlen + 1; }
  constraint wstrb_c2 { wstrb.size() == awlen + 1; }

  // Element constraints (will be skipped)
  constraint wstrb_c3 { foreach(wstrb[i]) wstrb[i] != 0; }

  function new();
  endfunction
endclass

module t;
  initial begin
    queue_test obj = new();
    int success;

    $display("Testing queue with size == awlen + 1...");

    success = obj.randomize();

    if (success) begin
      $display("Randomization succeeded: awlen=%0d, wdata.size=%0d, wstrb.size=%0d",
               obj.awlen, obj.wdata.size(), obj.wstrb.size());

      if (obj.wdata.size() == obj.awlen + 1) begin
        $display("[PASS] wdata.size matches awlen+1");
      end else begin
        $display("[FAIL] wdata.size (%0d) != awlen+1 (%0d)", obj.wdata.size(), obj.awlen + 1);
      end

      if (obj.wstrb.size() == obj.awlen + 1) begin
        $display("[PASS] wstrb.size matches awlen+1");
      end else begin
        $display("[FAIL] wstrb.size (%0d) != awlen+1 (%0d)", obj.wstrb.size(), obj.awlen + 1);
      end

    end else begin
      $display("[FAIL] Randomization failed");
    end

    $display("*-* All Finished *-*");
    $finish;
  end
endmodule
