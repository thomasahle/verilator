// DESCRIPTION: Verilator: Test queue with enum in size expression
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off CONSTRAINTIGN */
/* verilator lint_off WIDTHEXPAND */
/* verilator lint_off WIDTHTRUNC */
typedef enum logic [2:0] {
  SIZE_1 = 3'b000,
  SIZE_2 = 3'b001,
  SIZE_4 = 3'b010
} size_e;

class queue_test;
  rand bit [7:0] awlen;
  rand size_e awsize;
  rand bit [31:0] wdata [$:256];
  rand bit [3:0] wstrb [$:256];

  constraint len_c { awlen inside {[0:3]}; }
  constraint size_c { awsize inside {SIZE_1, SIZE_2}; }

  // Size constraint
  constraint wdata_c1 { wdata.size() == awlen + 1; }
  constraint wstrb_c2 { wstrb.size() == awlen + 1; }

  // Element constraint with $countones and enum exponent
  constraint wstrb_c3 { foreach(wstrb[i]) wstrb[i] != 0; }
  constraint wstrb_c4 { foreach(wstrb[i]) $countones(wstrb[i]) == 2**awsize; }

  function new();
  endfunction
endclass

module t;
  initial begin
    queue_test obj = new();
    int success;

    $display("Testing queue with enum in constraints...");

    success = obj.randomize();

    if (success) begin
      $display("Randomization succeeded:");
      $display("  awlen = %0d", obj.awlen);
      $display("  awsize = %s (%0d)", obj.awsize.name(), obj.awsize);
      $display("  wdata.size = %0d", obj.wdata.size());
      $display("  wstrb.size = %0d", obj.wstrb.size());

      if (obj.wdata.size() == obj.awlen + 1) begin
        $display("[PASS] wdata.size matches awlen+1");
      end else begin
        $display("[FAIL] wdata.size (%0d) != awlen+1 (%0d)", obj.wdata.size(), obj.awlen + 1);
      end

    end else begin
      $display("[FAIL] Randomization failed");
    end

    $display("*-* All Finished *-*");
    $finish;
  end
endmodule
