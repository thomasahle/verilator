// DESCRIPTION: Verilator: Test $ (maximum value) in covergroup bin ranges
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test that $ in bin ranges means maximum value for the type

module t;
    bit [3:0] val4;  // 4-bit: max is 15
    bit [7:0] val8;  // 8-bit: max is 255

    covergroup cg4;
        // $ should represent 15 for 4-bit value
        cp: coverpoint val4 {
            bins low = {[0:7]};      // 0-7
            bins high = {[8:$]};     // 8-15 ($ = 15)
        }
    endgroup

    covergroup cg8;
        // $ should represent 255 for 8-bit value
        cp: coverpoint val8 {
            bins low = {[0:127]};     // 0-127
            bins high = {[128:$]};    // 128-255 ($ = 255)
        }
    endgroup

    cg4 cg4_inst;
    cg8 cg8_inst;

    initial begin
        cg4_inst = new();
        cg8_inst = new();

        // Test 4-bit covergroup
        val4 = 4'd5;  // Should hit 'low' bin
        cg4_inst.sample();
        $display("After val4=5: coverage=%0.2f%%", cg4_inst.get_inst_coverage());

        val4 = 4'd15;  // Should hit 'high' bin (max value)
        cg4_inst.sample();
        $display("After val4=15: coverage=%0.2f%%", cg4_inst.get_inst_coverage());

        if (cg4_inst.get_inst_coverage() >= 99.0) begin
            $display("PASS: 4-bit $ range test passed");
        end else begin
            $display("FAIL: 4-bit $ range expected 100%%, got %0.2f%%", cg4_inst.get_inst_coverage());
        end

        // Test 8-bit covergroup
        val8 = 8'd50;  // Should hit 'low' bin
        cg8_inst.sample();
        $display("After val8=50: coverage=%0.2f%%", cg8_inst.get_inst_coverage());

        val8 = 8'd255;  // Should hit 'high' bin (max value)
        cg8_inst.sample();
        $display("After val8=255: coverage=%0.2f%%", cg8_inst.get_inst_coverage());

        if (cg8_inst.get_inst_coverage() >= 99.0) begin
            $display("PASS: 8-bit $ range test passed");
        end else begin
            $display("FAIL: 8-bit $ range expected 100%%, got %0.2f%%", cg8_inst.get_inst_coverage());
        end

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
