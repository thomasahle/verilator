// DESCRIPTION: Verilator: Test coverpoints with expressions
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Anthropic.
// SPDX-License-Identifier: CC0-1.0

// Test for coverpoints containing binary expressions
// Regression test for V3Width segfault when coverpoints use
// expressions like `5 * 8` or `val + 1`

module t;

  int val;

  // Module-level covergroup with expression in coverpoint
  covergroup cg_module_expr;
    option.per_instance = 1;

    // Constant multiplication - was causing segfault
    CP_CONST_MUL : coverpoint 5 * 8 {
      bins B40 = {40};
    }

    // Constant addition - was causing segfault
    CP_CONST_ADD : coverpoint 3 + 7 {
      bins B10 = {10};
    }

    // Variable with addition - was causing segfault
    CP_VAR_ADD : coverpoint val + 1 {
      bins LOW = {[0:10]};
      bins HIGH = {[11:100]};
    }

    // Variable with multiplication - was causing segfault
    CP_VAR_MUL : coverpoint val * 2 {
      bins LOW = {[0:20]};
      bins HIGH = {[21:200]};
    }

    // Complex expression
    CP_COMPLEX : coverpoint (val + 10) * 2 {
      bins LOW = {[0:50]};
      bins HIGH = {[51:500]};
    }

    // Division and subtraction
    CP_DIV : coverpoint val / 2 {
      bins LOW = {[0:10]};
      bins HIGH = {[11:100]};
    }

    CP_SUB : coverpoint val - 5 {
      bins NEG = {[-10:-1]};
      bins POS = {[0:100]};
    }

    // Bitwise operations
    CP_AND : coverpoint val & 8'hFF {
      bins LOW = {[0:127]};
      bins HIGH = {[128:255]};
    }

    CP_OR : coverpoint val | 8'h01 {
      bins ODD = {[1:255]};
    }
  endgroup

  cg_module_expr m_cg = new;

  initial begin
    // Sample with low value
    val = 5;
    m_cg.sample();

    // Sample with high value
    val = 50;
    m_cg.sample();

    // Sample with another value to hit more bins
    val = 200;
    m_cg.sample();

    $display("Module coverage: %0.2f%%", m_cg.get_inst_coverage());

    // Verify we don't crash and get reasonable coverage
    if (m_cg.get_inst_coverage() > 0.0) begin
      $display("Coverage is non-zero - expressions working correctly");
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
