// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
    // Inputs
    clk
    );

    input clk;
    logic [3:0]  a;
    int   b;
    int cyc = 0;

    always @(posedge clk) begin
        cyc <= cyc + 1;
    end

    covergroup cg @(posedge clk);
        coverpoint a;
        coverpoint b {
            bins the_bins [5] = { [0:20] };
        }
    endgroup

    cg the_cg = new;

    assign a = cyc[3:0];
    assign b = cyc;

    always @(posedge clk) begin
        if (cyc == 14) begin
            $display("coverage a = %f", the_cg.a.get_inst_coverage());
            $display("coverage b = %f", the_cg.b.get_inst_coverage());
            // a is 4-bit, so 16 auto bins, we've covered 15 values (0-14)
            if (the_cg.a.get_inst_coverage() < 90.0) $stop;
            // b has 5 explicit bins, all values 0-13 should hit at least 4 of them
            if (the_cg.b.get_inst_coverage() < 80.0) $stop;
            $write("*-* All Finished *-*\n");
            $finish;
        end
    end
endmodule
