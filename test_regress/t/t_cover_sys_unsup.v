// DESCRIPTION: Verilator: Test for coverage system functions
//
// The coverage system functions ($coverage_control, $coverage_get, etc.)
// are implemented as stubs that return 0 for success or no-ops.
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
  real r;
  int i;
  string s;

  initial begin
    // Test coverage system functions (stub implementations return 0)
    // control_constant: SV_COV_START=0, SV_COV_STOP=1, SV_COV_RESET=2, SV_COV_CHECK=3
    // coverage_type: SV_COV_ASSERTION=1, SV_COV_FSM_STATE=2, SV_COV_STATEMENT=3, SV_COV_TOGGLE=23
    // scope_def: SV_COV_MODULE=10, SV_COV_HIER=11

    i = $coverage_control(0, 23, 10, $root);
    if (i !== 0) $stop;

    i = $coverage_get(23, 10, $root);
    if (i !== 0) $stop;

    i = $coverage_get_max(23, 10, $root);
    if (i !== 0) $stop;

    r = $get_coverage();
    if (r != 0.0) $stop;

    $set_coverage_db_name("filename");

    i = $coverage_save(23, "filename");
    if (i !== 0) $stop;

    $load_coverage_db("filename");

    i = $coverage_merge(23, "filename");
    if (i !== 0) $stop;

    $write("*-* All Coverage System Function Tests Passed\n");
    $finish;
  end

endmodule
