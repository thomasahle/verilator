// DESCRIPTION: Verilator: Test option.cross_auto_bin_max for cross coverage
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test option.cross_auto_bin_max - limits number of auto-generated cross bins

module t;
    bit [2:0] a, b;

    // Covergroup with unlimited cross bins (3 x 3 = 9 bins)
    covergroup cg_unlimited;
        option.per_instance = 1;
        cp_a: coverpoint a {
            bins low = {0, 1, 2};
            bins mid = {3, 4};
            bins high = {5, 6, 7};
        }
        cp_b: coverpoint b {
            bins low = {0, 1, 2};
            bins mid = {3, 4};
            bins high = {5, 6, 7};
        }
        // 3 x 3 = 9 cross bins - should be generated
        cross_ab: cross cp_a, cp_b;
    endgroup

    // Covergroup with cross_auto_bin_max = 5 (would have 9 bins, exceeds limit)
    covergroup cg_limited;
        option.per_instance = 1;
        option.cross_auto_bin_max = 5;  // Limit to 5 cross bins
        cp_a: coverpoint a {
            bins low = {0, 1, 2};
            bins mid = {3, 4};
            bins high = {5, 6, 7};
        }
        cp_b: coverpoint b {
            bins low = {0, 1, 2};
            bins mid = {3, 4};
            bins high = {5, 6, 7};
        }
        // 3 x 3 = 9 cross bins, exceeds limit of 5, should be skipped
        cross_ab: cross cp_a, cp_b;
    endgroup

    // Covergroup with cross_auto_bin_max = 10 (9 bins, under limit)
    covergroup cg_under_limit;
        option.per_instance = 1;
        option.cross_auto_bin_max = 10;  // Limit to 10 cross bins
        cp_a: coverpoint a {
            bins low = {0, 1, 2};
            bins mid = {3, 4};
            bins high = {5, 6, 7};
        }
        cp_b: coverpoint b {
            bins low = {0, 1, 2};
            bins mid = {3, 4};
            bins high = {5, 6, 7};
        }
        // 3 x 3 = 9 cross bins, under limit of 10, should be generated
        cross_ab: cross cp_a, cp_b;
    endgroup

    cg_unlimited cg_unlimited_inst;
    cg_limited cg_limited_inst;
    cg_under_limit cg_under_limit_inst;

    initial begin
        cg_unlimited_inst = new();
        cg_limited_inst = new();
        cg_under_limit_inst = new();

        // Sample some values
        a = 0; b = 0;
        cg_unlimited_inst.sample();
        cg_limited_inst.sample();
        cg_under_limit_inst.sample();

        a = 3; b = 5;
        cg_unlimited_inst.sample();
        cg_limited_inst.sample();
        cg_under_limit_inst.sample();

        a = 7; b = 7;
        cg_unlimited_inst.sample();
        cg_limited_inst.sample();
        cg_under_limit_inst.sample();

        // Check coverage
        // cg_unlimited should have cross coverage (9 bins, 3 hit = 33.33%)
        // cg_limited should have 0% or 100% coverage (cross was skipped)
        // cg_under_limit should have cross coverage (9 bins, 3 hit = 33.33%)
        $display("cg_unlimited coverage: %0.2f%%", cg_unlimited_inst.get_inst_coverage());
        $display("cg_limited coverage: %0.2f%%", cg_limited_inst.get_inst_coverage());
        $display("cg_under_limit coverage: %0.2f%%", cg_under_limit_inst.get_inst_coverage());

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
