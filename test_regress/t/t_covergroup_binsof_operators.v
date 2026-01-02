// DESCRIPTION: Verilator: Test binsof() with && and || operators
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off WIDTHTRUNC */

module t;
    bit [2:0] a, b;

    // Covergroup with ignore_bins using && operator
    covergroup cg_and;
        cp_a: coverpoint a {
            bins low = {[0:3]};
            bins high = {[4:7]};
        }
        cp_b: coverpoint b {
            bins low = {[0:3]};
            bins high = {[4:7]};
        }

        // Cross with binsof() using && operator
        // Ignores when both a and b are in low bins (low && low)
        cross_ab: cross cp_a, cp_b {
            ignore_bins both_low = binsof(cp_a.low) && binsof(cp_b.low);
        }
    endgroup

    // Covergroup with ignore_bins using || operator
    covergroup cg_or;
        cp_a: coverpoint a {
            bins low = {[0:3]};
            bins high = {[4:7]};
        }
        cp_b: coverpoint b {
            bins low = {[0:3]};
            bins high = {[4:7]};
        }

        // Cross with binsof() using || operator
        // Ignores when either a or b is in low bins
        cross_ab: cross cp_a, cp_b {
            ignore_bins any_low = binsof(cp_a.low) || binsof(cp_b.low);
        }
    endgroup

    cg_and cg_and_inst;
    cg_or cg_or_inst;

    real coverage;

    initial begin
        cg_and_inst = new();
        cg_or_inst = new();

        // Test 1: Sample only high values (a=4, b=4)
        // This should hit: cp_a.high, cp_b.high, and cross high_high
        a = 4; b = 4;
        cg_and_inst.sample();
        cg_or_inst.sample();

        // For cg_and:
        // - cp_a: 2 bins (hit 1), cp_b: 2 bins (hit 1), cross: 3 bins (hit 1)
        // - Total: 7 bins, hit: 3 => 42.86%
        coverage = cg_and_inst.get_inst_coverage();
        $display("cg_and after (high,high): %0.2f%%", coverage);
        if (coverage < 42.0 || coverage > 43.0) begin
            $display("%%Error: Expected ~42.86%%, got %0.2f%%", coverage);
            $stop;
        end

        // For cg_or:
        // - Cross only has 1 bin (high_high, others ignored)
        // - Total: 5 bins, hit: 3 => 60%
        coverage = cg_or_inst.get_inst_coverage();
        $display("cg_or after (high,high): %0.2f%%", coverage);
        if (coverage < 59.0 || coverage > 61.0) begin
            $display("%%Error: Expected ~60.00%%, got %0.2f%%", coverage);
            $stop;
        end

        // Test 2: Sample low values (a=0, b=0)
        // For cg_and: should NOT create low_low cross bin (it was ignored)
        // But low_high and high_low will be hit because constituent bins are now all hit
        // For cg_or: cross bin only has high_high, so hitting low coverpoint bins doesn't add cross hits
        a = 0; b = 0;
        cg_and_inst.sample();
        cg_or_inst.sample();

        // For cg_and:
        // - cp_a: 2 bins (hit 2), cp_b: 2 bins (hit 2)
        // - cross: 3 bins (low_high, high_low, high_high) - all now hit because their
        //   constituent coverpoint bins have been hit across samples
        //   (low_low was never generated due to ignore_bins - this is the test!)
        // - Total: 7 bins, hit: 7 => 100%
        coverage = cg_and_inst.get_inst_coverage();
        $display("cg_and after (low,low): %0.2f%%", coverage);
        if (coverage < 99.0 || coverage > 101.0) begin
            $display("%%Error: Expected 100%%, got %0.2f%%", coverage);
            $stop;
        end

        // For cg_or:
        // - cp_a: 2 bins (hit 2), cp_b: 2 bins (hit 2), cross: 1 bin (hit 1)
        // - Total: 5 bins, hit: 5 => 100%
        coverage = cg_or_inst.get_inst_coverage();
        $display("cg_or after (low,low): %0.2f%%", coverage);
        if (coverage < 99.0 || coverage > 101.0) begin
            $display("%%Error: Expected 100%%, got %0.2f%%", coverage);
            $stop;
        end

        $display("Coverage: %0.2f%%", cg_and_inst.get_inst_coverage());

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
