// DESCRIPTION: Verilator: Verilog Test module
//
// Test bounded queue randomization with [$:N] syntax
// Pattern found in mbits-mirafra AVIPs
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Anthropic.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define check_range(gotv,minv,maxv) do if ((gotv) < (minv) || (gotv) > (maxv)) begin $write("%%Error: %s:%0d:  got=%0d not in range [%0d:%0d]\n", `__FILE__,`__LINE__, (gotv), (minv), (maxv)); `stop; end while(0);

// Test class with bounded queue - simulates AXI4 transaction data
class Axi4Transaction;
    parameter int DATA_WIDTH = 32;
    parameter int MAX_LENGTH = 8;

    rand bit [7:0] length;  // Burst length
    rand bit [DATA_WIDTH-1:0] wdata [$:MAX_LENGTH];  // Bounded queue

    constraint length_c {
        length inside {[1:MAX_LENGTH]};
    }

    constraint wdata_size_c {
        wdata.size() == length;
    }

    constraint wdata_values_c {
        foreach (wdata[i]) {
            wdata[i] inside {[32'h0000_0000:32'hFFFF_FFFF]};
        }
    }

    function new();
        length = 1;
        wdata = {};
    endfunction

    function void check();
        `check_range(wdata.size(), 1, MAX_LENGTH)
        `checkh(wdata.size(), length)
    endfunction
endclass

// Test class with bounded queue and complex constraints
class BurstTransaction;
    rand bit [3:0] burst_len;
    rand bit [31:0] addr_queue [$:16];
    rand bit [63:0] data_queue [$:16];

    constraint burst_c {
        burst_len inside {[1:8]};
        addr_queue.size() == burst_len;
        data_queue.size() == burst_len;
    }

    constraint addr_sequential_c {
        foreach (addr_queue[i]) {
            if (i > 0) addr_queue[i] == addr_queue[i-1] + 4;
        }
    }

    constraint data_pattern_c {
        foreach (data_queue[i]) {
            data_queue[i][31:0] == addr_queue[i];
        }
    }

    function new();
        burst_len = 1;
        addr_queue = {};
        data_queue = {};
    endfunction

    function void check();
        `check_range(addr_queue.size(), 1, 8)
        `checkh(addr_queue.size(), burst_len)
        `checkh(data_queue.size(), burst_len)
        for (int i = 1; i < addr_queue.size(); i++) begin
            `checkh(addr_queue[i], addr_queue[i-1] + 4)
        end
        for (int i = 0; i < data_queue.size(); i++) begin
            `checkh(data_queue[i][31:0], addr_queue[i])
        end
    endfunction
endclass

module t_constraint_queue_bounded;
    Axi4Transaction axi_tx;
    BurstTransaction burst_tx;
    int success;

    initial begin
        $display("Test: Bounded queue randomization");

        // Test Axi4Transaction
        axi_tx = new();
        repeat(5) begin
            success = axi_tx.randomize();
            `checkh(success, 1)
            axi_tx.check();
            $display("  AXI4: length=%0d, wdata.size=%0d", axi_tx.length, axi_tx.wdata.size());
        end

        // Test BurstTransaction
        burst_tx = new();
        repeat(5) begin
            success = burst_tx.randomize();
            `checkh(success, 1)
            burst_tx.check();
            $display("  Burst: len=%0d, addr[0]=0x%h", burst_tx.burst_len, burst_tx.addr_queue[0]);
        end

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
