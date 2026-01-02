// DESCRIPTION: Verilator: Test wildcard bins in covergroup
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test wildcard bins using ? to match multiple values

module t;
    bit [3:0] val;

    covergroup cg;
        cp: coverpoint val {
            // Wildcard bin matching 0x0? (low nibble any value, high nibble 0)
            // In 4 bits, this matches 0-15 but the syntax uses ? for "any"
            // wildcard bins low_half = {4'b00??};  // matches 0,1,2,3
            // wildcard bins high_half = {4'b11??}; // matches 12,13,14,15
            wildcard bins low = {4'b00??};   // matches 0-3
            wildcard bins mid = {4'b01??};   // matches 4-7
            wildcard bins high = {4'b1???};  // matches 8-15
        }
    endgroup

    cg cg_inst;

    initial begin
        cg_inst = new();

        // Sample value 2 (0b0010) - should hit "low" bin
        val = 4'd2;
        cg_inst.sample();
        $display("After val=2: coverage=%0.2f%%", cg_inst.get_inst_coverage());

        // Sample value 5 (0b0101) - should hit "mid" bin
        val = 4'd5;
        cg_inst.sample();
        $display("After val=5: coverage=%0.2f%%", cg_inst.get_inst_coverage());

        // Sample value 10 (0b1010) - should hit "high" bin
        val = 4'd10;
        cg_inst.sample();
        $display("After val=10: coverage=%0.2f%%", cg_inst.get_inst_coverage());

        // Note: wildcard bins with ? syntax not yet implemented
        // Currently, ? characters are treated as 0 bits
        // So coverage is 0% because we sample 2, 5, 10 but bins only match 0, 4, 8
        // This test documents current behavior - to be fixed in future
        $display("Note: wildcard bins with ? not yet fully implemented");
        $display("Current coverage: %0.2f%% (expected 0%% until feature implemented)",
                 cg_inst.get_inst_coverage());

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
