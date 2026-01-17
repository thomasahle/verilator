// DESCRIPTION: Verilator: Test $root in coverage function arguments
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test that $root can be used standalone and in dotted expressions
// as arguments to coverage functions (IEEE 1800-2017 23.3.1, 21.8)

module DUT;
endmodule

module t();
    int unsigned i;
    real r;
    DUT unit1();
    DUT unit2();

    initial begin
        // Test $root standalone
        // Using numeric values: 3=check, 23=toggle, 11=hier
        i = $coverage_control(3, 23, 11, $root);

        // Test $root.module.instance
        i = $coverage_control(3, 23, 11, $root.t.unit1);
        i = $coverage_control(3, 23, 11, $root.t.unit2);

        // Test $coverage_get with $root
        r = $coverage_get(23, 11, $root.t.unit1);

        // Test $get_coverage (no args)
        r = $get_coverage();

        // Test $set_coverage_db_name and $load_coverage_db
        $set_coverage_db_name("coverage.db");
        $load_coverage_db("coverage.db");

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
