// DESCRIPTION: Verilator: Test binsof() with intersect clause
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off WIDTHTRUNC */

module t;
    bit [2:0] a, b;

    // Covergroup with ignore_bins using intersect clause
    covergroup cg_intersect;
        cp_a: coverpoint a {
            bins low = {[0:3]};
            bins high = {[4:7]};
        }
        cp_b: coverpoint b {
            bins low = {[0:3]};
            bins high = {[4:7]};
        }

        // Cross with binsof() using intersect
        // Ignore combinations where cp_a is in low range (0-3)
        // This should ignore: low_low, low_high (any cross with cp_a.low)
        cross_ab: cross cp_a, cp_b {
            ignore_bins ignore_low_a = binsof(cp_a) intersect {0, 1, 2, 3};
        }
    endgroup

    // Covergroup with specific bin intersect
    covergroup cg_intersect_bin;
        cp_a: coverpoint a {
            bins b0 = {0};
            bins b1 = {1};
            bins b2 = {2};
            bins b3 = {3};
        }
        cp_b: coverpoint b {
            bins low = {[0:3]};
            bins high = {[4:7]};
        }

        // Ignore only when cp_a.b0 or cp_a.b1 (values 0 or 1)
        cross_ab: cross cp_a, cp_b {
            ignore_bins ignore_01 = binsof(cp_a) intersect {0, 1};
        }
    endgroup

    cg_intersect cg_intersect_inst;
    cg_intersect_bin cg_intersect_bin_inst;

    real coverage;

    initial begin
        cg_intersect_inst = new();
        cg_intersect_bin_inst = new();

        // Test 1: Sample only high values (a=4, b=4)
        // For cg_intersect:
        // - cp_a: 2 bins (low, high), cp_b: 2 bins (low, high)
        // - Cross without ignore would have 4 bins: low_low, low_high, high_low, high_high
        // - With ignore_bins using intersect {[0:3]}, cp_a.low bins are ignored
        // - Remaining cross bins: high_low, high_high (2 bins)
        // - Total bins: 2 + 2 + 2 = 6
        a = 4; b = 4;
        cg_intersect_inst.sample();

        // After (high,high): cp_a.high hit, cp_b.high hit, high_high cross hit
        // 3 out of 6 bins hit = 50%
        coverage = cg_intersect_inst.get_inst_coverage();
        $display("cg_intersect after (high,high): %0.2f%%", coverage);
        if (coverage < 49.0 || coverage > 51.0) begin
            $display("%%Error: Expected ~50%%, got %0.2f%%", coverage);
            $stop;
        end

        // Test 2: Sample (a=0, b=4) - low_high combination
        // This should NOT create a cross bin hit (it was ignored)
        a = 0; b = 4;
        cg_intersect_inst.sample();

        // Now: cp_a.low hit, cp_b.high already hit
        // cp_a bins: 2 (both hit), cp_b bins: 1 hit of 2, cross: 1 hit of 2
        // Total: 4 of 6 = 66.67%
        coverage = cg_intersect_inst.get_inst_coverage();
        $display("cg_intersect after (low,high): %0.2f%%", coverage);
        if (coverage < 65.0 || coverage > 68.0) begin
            $display("%%Error: Expected ~66.67%%, got %0.2f%%", coverage);
            $stop;
        end

        // Test 3: Complete coverage
        a = 4; b = 0;
        cg_intersect_inst.sample();

        // All coverpoint bins hit, both remaining cross bins hit
        // Total: 6 of 6 = 100%
        coverage = cg_intersect_inst.get_inst_coverage();
        $display("cg_intersect after (high,low): %0.2f%%", coverage);
        if (coverage < 99.0 || coverage > 101.0) begin
            $display("%%Error: Expected 100%%, got %0.2f%%", coverage);
            $stop;
        end

        // Test cg_intersect_bin
        // cp_a has 4 bins, cp_b has 2 bins
        // Cross would have 8 bins, but ignore_bins removes where cp_a is 0 or 1
        // That's b0_low, b0_high, b1_low, b1_high = 4 bins removed
        // Remaining: b2_low, b2_high, b3_low, b3_high = 4 cross bins
        // Total bins: 4 + 2 + 4 = 10

        a = 2; b = 4;
        cg_intersect_bin_inst.sample();

        // cp_a.b2 hit, cp_b.high hit, b2_high cross hit
        // 3 of 10 = 30%
        coverage = cg_intersect_bin_inst.get_inst_coverage();
        $display("cg_intersect_bin after (2,high): %0.2f%%", coverage);
        if (coverage < 29.0 || coverage > 31.0) begin
            $display("%%Error: Expected ~30%%, got %0.2f%%", coverage);
            $stop;
        end

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
