// DESCRIPTION: Verilator: Test covergroup with function sample
// Pattern from SPI AVIP: covergroup cg with function sample(Config cfg, Packet pkt);
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off WIDTHTRUNC */

class Config;
    rand bit [3:0] mode;
    rand bit [7:0] delay;

    function new();
        mode = 0;
        delay = 10;
    endfunction
endclass

class Packet;
    rand bit [31:0] data;
    rand bit [7:0] size;

    function new();
        data = 0;
        size = 8;
    endfunction
endclass

class CoverageCollector;
    // Covergroup with function sample - pattern from AVIPs
    covergroup cg with function sample(Config cfg, Packet pkt);
        option.per_instance = 1;

        // Coverpoint using function argument
        MODE_CP: coverpoint cfg.mode {
            bins mode0 = {0};
            bins mode1 = {1};
            bins mode2 = {2};
            bins mode3 = {3};
        }

        // Another coverpoint using different argument
        SIZE_CP: coverpoint pkt.size {
            bins sz_small = {[1:16]};
            bins sz_medium = {[17:64]};
            bins sz_large = {[65:255]};
        }

        // Coverpoint with expression on argument
        DATA_MSB_CP: coverpoint pkt.data[31:24] {
            bins zero = {0};
            bins nonzero = {[1:255]};
        }

        // Cross of function arguments
        MODE_X_SIZE: cross MODE_CP, SIZE_CP;
    endgroup

    function new();
        cg = new();
    endfunction

    function void collect(Config cfg, Packet pkt);
        cg.sample(cfg, pkt);
    endfunction

    function real get_coverage();
        return cg.get_inst_coverage();
    endfunction
endclass

module t;
    CoverageCollector collector;
    Config cfg;
    Packet pkt;
    real coverage;

    initial begin
        collector = new();
        cfg = new();
        pkt = new();

        // Sample 1: mode=0, size=8 (small), data MSB=0
        cfg.mode = 0;
        pkt.size = 8;
        pkt.data = 32'h00_12_34_56;
        collector.collect(cfg, pkt);

        // Expected bins hit: mode0, sz_small, zero, mode0_sz_small cross
        // MODE_CP: 4 bins, SIZE_CP: 3 bins, DATA_MSB_CP: 2 bins, cross: 12 bins
        // Total: 21 bins, 4 hit = 19%
        coverage = collector.get_coverage();
        $display("After sample 1: %.2f%%", coverage);
        if (coverage < 18.0 || coverage > 20.0) begin
            $display("%%Error: Expected ~19%%, got %.2f%%", coverage);
            $stop;
        end

        // Sample 2: mode=1, size=32 (medium), data MSB=0xFF
        cfg.mode = 1;
        pkt.size = 32;
        pkt.data = 32'hFF_00_00_00;
        collector.collect(cfg, pkt);

        // Additional hits: mode1, sz_medium, nonzero
        // Cross bins use persistent hits: mode0_sz_medium, mode1_sz_small, mode1_sz_medium
        // Total: 10 of 21 = 47.6%
        coverage = collector.get_coverage();
        $display("After sample 2: %.2f%%", coverage);
        if (coverage < 46.0 || coverage > 49.0) begin
            $display("%%Error: Expected ~47.6%%, got %.2f%%", coverage);
            $stop;
        end

        // Sample 3: mode=2, size=100 (large)
        cfg.mode = 2;
        pkt.size = 100;
        pkt.data = 32'h00_FF_FF_FF;
        collector.collect(cfg, pkt);

        coverage = collector.get_coverage();
        $display("After sample 3: %.2f%%", coverage);

        // Sample 4: mode=3
        cfg.mode = 3;
        pkt.size = 200;
        pkt.data = 32'hAB_CD_EF_00;
        collector.collect(cfg, pkt);

        coverage = collector.get_coverage();
        $display("Final coverage: %.2f%%", coverage);

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
