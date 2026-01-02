// DESCRIPTION: Verilator: Test auto-bin generation for coverpoints
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test automatic bin generation when coverpoint has no explicit bins
// verilator lint_off WIDTHTRUNC
// verilator lint_off CMPCONST

module t;
  bit [3:0] value4;  // 16 possible values

  covergroup cg;
    // Coverpoint WITHOUT explicit bins - should auto-generate 16 bins
    cp_auto4: coverpoint value4;
  endgroup

  cg cg_inst;

  initial begin
    cg_inst = new();

    // Test 4-bit auto bins (should be 16 bins, one per value)
    for (int i = 0; i < 16; i++) begin
      value4 = i[3:0];
      cg_inst.sample();
    end
    $display("4-bit coverage: %0.1f%%", cg_inst.get_inst_coverage());

    if (cg_inst.get_inst_coverage() == 100.0) begin
      $write("*-* All Finished *-*\n");
    end else begin
      $display("FAIL: Expected 100%% coverage, got %0.1f%%", cg_inst.get_inst_coverage());
    end
    $finish;
  end
endmodule
