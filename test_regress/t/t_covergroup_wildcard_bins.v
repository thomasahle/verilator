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

        // Wildcard bins now work with mask-based matching
        // All 3 bins should be hit: val=2 matches 4'b00??, val=5 matches 4'b01??, val=10 matches 4'b1???
        if (cg_inst.get_inst_coverage() >= 99.0) begin
            $display("PASS: All wildcard bins hit, coverage=100%%");
        end else begin
            $display("FAIL: Expected 100%% coverage, got %0.2f%%", cg_inst.get_inst_coverage());
        end

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
