// DESCRIPTION: Verilator: Test default bin for coverpoints
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test default bins - should match when no other bin matches
// verilator lint_off WIDTHTRUNC
// verilator lint_off CMPCONST

module t;
  bit [3:0] value;  // 16 possible values

  covergroup cg;
    // Coverpoint with explicit bins and a default bin
    cp_with_default: coverpoint value {
      bins low = {[0:3]};     // Values 0-3
      bins mid = {[4:7]};     // Values 4-7
      bins high = {[8:11]};   // Values 8-11
      bins others = default;  // Values 12-15 (everything else)
    }
  endgroup

  cg cg_inst;

  int low_count, mid_count, high_count, others_count;

  initial begin
    cg_inst = new();

    // Test all 16 values
    for (int i = 0; i < 16; i++) begin
      value = i[3:0];
      cg_inst.sample();
    end

    $display("Coverage: %0.1f%%", cg_inst.get_inst_coverage());

    // Should have 100% coverage (4 bins, each hit at least once)
    if (cg_inst.get_inst_coverage() == 100.0) begin
      $write("*-* All Finished *-*\n");
    end else begin
      $display("FAIL: Expected 100%% coverage, got %0.1f%%", cg_inst.get_inst_coverage());
    end
    $finish;
  end
endmodule
