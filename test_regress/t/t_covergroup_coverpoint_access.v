// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class TestCov;
    int data;
    int mode;

    covergroup cg;
        DATA_CP: coverpoint data {
            bins low = {[0:7]};
            bins high = {[8:15]};
        }
        MODE_CP: coverpoint mode {
            bins zero = {0};
            bins one = {1};
            bins two = {2};
            bins three = {3};
        }
    endgroup

    function new();
        cg = new;
    endfunction
endclass

module t;
    TestCov tc;
    initial begin
        tc = new;

        // Initially all bins are 0%
        // Test per-coverpoint coverage access
        tc.data = 5;  // hits 'low' bin
        tc.mode = 0;  // hits 'zero' bin
        tc.cg.sample();

        // DATA_CP: 1/2 = 50%, MODE_CP: 1/4 = 25%
        if (tc.cg.DATA_CP.get_inst_coverage() != 50.0) begin
            $display("ERROR: DATA_CP expected 50.0, got %f", tc.cg.DATA_CP.get_inst_coverage());
            $stop;
        end
        if (tc.cg.MODE_CP.get_inst_coverage() != 25.0) begin
            $display("ERROR: MODE_CP expected 25.0, got %f", tc.cg.MODE_CP.get_inst_coverage());
            $stop;
        end

        // Hit more bins
        tc.data = 10; // hits 'high' bin
        tc.mode = 2;  // hits 'two' bin
        tc.cg.sample();

        // DATA_CP: 2/2 = 100%, MODE_CP: 2/4 = 50%
        if (tc.cg.DATA_CP.get_inst_coverage() != 100.0) begin
            $display("ERROR: DATA_CP expected 100.0, got %f", tc.cg.DATA_CP.get_inst_coverage());
            $stop;
        end
        if (tc.cg.MODE_CP.get_inst_coverage() != 50.0) begin
            $display("ERROR: MODE_CP expected 50.0, got %f", tc.cg.MODE_CP.get_inst_coverage());
            $stop;
        end

        // Verify overall coverage matches sum of coverpoints
        // Overall = (2 + 2) / (2 + 4) = 4/6 = 66.67%
        if (tc.cg.get_inst_coverage() < 66.0 || tc.cg.get_inst_coverage() > 67.0) begin
            $display("ERROR: Overall expected ~66.67, got %f", tc.cg.get_inst_coverage());
            $stop;
        end

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
