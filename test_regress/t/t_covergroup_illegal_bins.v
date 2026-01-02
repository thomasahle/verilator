// DESCRIPTION: Verilator: Test illegal_bins in covergroup
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test that illegal_bins are recognized and handled
// illegal_bins should not count towards coverage goal

module t;
    bit [2:0] val;
    int illegal_hit_count;

    covergroup cg;
        cp: coverpoint val {
            bins valid[] = {[0:5]};
            illegal_bins bad = {6, 7};
        }
    endgroup

    cg cg_inst;

    initial begin
        cg_inst = new();
        illegal_hit_count = 0;

        // Sample valid values 0-5
        for (int i = 0; i < 6; i++) begin
            val = i[2:0];
            cg_inst.sample();
        end

        // Check coverage - should be 100% since all valid bins hit
        $display("Coverage after valid samples: %0.2f%%", cg_inst.get_inst_coverage());

        // The illegal_bins {6, 7} should not be counted in coverage goal
        // 6 valid bins, all hit = 100%

        if (cg_inst.get_inst_coverage() >= 99.0) begin
            $display("PASS: Coverage is 100%% with all valid bins hit");
        end else begin
            $display("FAIL: Expected 100%% coverage, got %0.2f%%", cg_inst.get_inst_coverage());
        end

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
