// DESCRIPTION: Verilator: Test binsof() with && and || operators
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off WIDTHTRUNC */

module t;
    bit [2:0] a, b;

    covergroup cg;
        cp_a: coverpoint a {
            bins low = {[0:3]};
            bins high = {[4:7]};
        }
        cp_b: coverpoint b {
            bins low = {[0:3]};
            bins high = {[4:7]};
        }

        // Cross with binsof() using && operator
        cross_ab: cross cp_a, cp_b {
            // Ignore when both a and b are in low bins
            ignore_bins both_low = binsof(cp_a.low) && binsof(cp_b.low);
        }
    endgroup

    cg cg_inst;

    initial begin
        cg_inst = new();

        // Sample all combinations of a and b
        for (int i = 0; i < 8; i++) begin
            for (int j = 0; j < 8; j++) begin
                a = i[2:0]; b = j[2:0];
                cg_inst.sample();
            end
        end

        // 2 coverpoints x 2 bins each + 1 cross with 4 bins = 8 bins total
        // Without ignore_bins: 8 bins, all should be hit = 100%
        // With ignore_bins both_low: 8 - 1 = 7 bins (ignore_bins don't count)
        // Currently: binsof() with && is ignored, so all 8 bins are counted
        $display("Coverage: %0.2f%%", cg_inst.get_inst_coverage());

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
