// DESCRIPTION: Verilator: Test negated binsof() with intersect clause
// Pattern from UART AVIP: !binsof(cp) intersect {value}
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off WIDTHTRUNC */

module t;
    typedef enum {FIVE_BIT, SIX_BIT, SEVEN_BIT, EIGHT_BIT} data_width_e;

    bit [7:0] data;
    data_width_e data_width;

    // Pattern from UART AVIP:
    // ignore_bins data_5 = !binsof(DATA_WIDTH_CP) intersect{FIVE_BIT};
    // This means: ignore all bins EXCEPT when DATA_WIDTH_CP is FIVE_BIT

    covergroup cg_negate_binsof;
        DATA_PATTERN: coverpoint data {
            bins pattern1 = {8'hFF};
            bins pattern2 = {8'hAA};
            bins pattern3 = {8'h00};
        }

        DATA_WIDTH_CP: coverpoint data_width {
            bins five = {FIVE_BIT};
            bins six = {SIX_BIT};
            bins seven = {SEVEN_BIT};
            bins eight = {EIGHT_BIT};
        }

        // Negated binsof: !binsof(DATA_WIDTH_CP) intersect {FIVE_BIT}
        // Ignore all cross bins where DATA_WIDTH_CP is NOT FIVE_BIT
        // Only keep cross bins where DATA_WIDTH_CP is FIVE_BIT
        PATTERN_X_WIDTH: cross DATA_PATTERN, DATA_WIDTH_CP {
            ignore_bins not_five = !binsof(DATA_WIDTH_CP) intersect {FIVE_BIT};
        }
    endgroup

    cg_negate_binsof cg;
    real coverage;

    initial begin
        cg = new();

        // Test 1: Sample with FIVE_BIT - this should create valid cross bins
        data = 8'hFF;
        data_width = FIVE_BIT;
        cg.sample();

        // DATA_PATTERN: 3 bins, DATA_WIDTH_CP: 4 bins
        // Cross would have 12 bins without ignore
        // With !binsof(DATA_WIDTH_CP) intersect {FIVE_BIT}:
        //   - ignore all cross bins where data_width is NOT FIVE_BIT
        //   - keep: pattern1_five, pattern2_five, pattern3_five (3 bins)
        // Total bins: 3 + 4 + 3 = 10

        // After sample: DATA_PATTERN.pattern1 hit, DATA_WIDTH_CP.five hit, pattern1_five cross hit
        // 3 of 10 = 30%
        coverage = cg.get_inst_coverage();
        $display("After (0xFF, FIVE_BIT): %0.2f%%", coverage);
        if (coverage < 29.0 || coverage > 31.0) begin
            $display("%%Error: Expected ~30%%, got %0.2f%%", coverage);
            $stop;
        end

        // Test 2: Sample with SIX_BIT
        // Note: Cross bins use persistent hit flags, so pattern2_five triggers
        // because DATA_WIDTH_CP.five was already hit and DATA_PATTERN.pattern2 is now hit
        data = 8'hAA;
        data_width = SIX_BIT;
        cg.sample();

        // DATA_PATTERN.pattern2 hit, DATA_WIDTH_CP.six hit
        // pattern2_five cross also hit (five still set from sample 1)
        // 6 of 10 = 60%
        coverage = cg.get_inst_coverage();
        $display("After (0xAA, SIX_BIT): %0.2f%%", coverage);
        if (coverage < 59.0 || coverage > 61.0) begin
            $display("%%Error: Expected ~60%%, got %0.2f%%", coverage);
            $stop;
        end

        // Test 3: Sample with pattern3 and SEVEN_BIT
        data = 8'h00;
        data_width = SEVEN_BIT;
        cg.sample();

        // DATA_PATTERN.pattern3 hit, DATA_WIDTH_CP.seven hit
        // pattern3_five cross also hit (five still set)
        // 9 of 10 = 90%
        coverage = cg.get_inst_coverage();
        $display("After (0x00, SEVEN_BIT): %0.2f%%", coverage);
        if (coverage < 89.0 || coverage > 91.0) begin
            $display("%%Error: Expected ~90%%, got %0.2f%%", coverage);
            $stop;
        end

        // Test 4: Complete remaining DATA_WIDTH_CP bin
        data_width = EIGHT_BIT;
        cg.sample();

        // All coverpoint bins hit, all cross bins hit
        // 10 of 10 = 100%
        coverage = cg.get_inst_coverage();
        $display("After all samples: %0.2f%%", coverage);
        if (coverage < 99.0 || coverage > 101.0) begin
            $display("%%Error: Expected 100%%, got %0.2f%%", coverage);
            $stop;
        end

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
