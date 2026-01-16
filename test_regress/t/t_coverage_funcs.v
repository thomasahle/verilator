// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test IEEE 1800-2017 21.8 Coverage system functions
// These are stub implementations that return 0

module t;
    initial begin
        int status;

        // $coverage_control - control coverage collection
        status = $coverage_control(1, 0, "all", "all");
        if (status !== 0) $stop;

        // $coverage_get - get coverage value
        status = $coverage_get(0, "all", "all");
        if (status !== 0) $stop;

        // $coverage_get_max - get maximum coverage value
        status = $coverage_get_max(0, "all", "all");
        if (status !== 0) $stop;

        // $coverage_merge - merge coverage data
        status = $coverage_merge("file.dat", "all");
        if (status !== 0) $stop;

        // $coverage_save - save coverage data
        status = $coverage_save("output.dat", "all");
        if (status !== 0) $stop;

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
