// DESCRIPTION: Verilator: Test bind with interface member access
// Test IEEE 1800-2017 section 23.11: bind expressions evaluated in bind source scope
// This tests the pattern used in AXI4 AVIP: binding modules that reference interface members
// from the source module scope
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// AXI4-like interface
interface axi4_if #(parameter DATA_WIDTH = 32) (input logic aclk, input logic aresetn);
    logic [DATA_WIDTH-1:0] awaddr;
    logic [DATA_WIDTH-1:0] wdata;
    logic [3:0] wstrb;
    logic wvalid;
    logic wready;
    logic [DATA_WIDTH-1:0] araddr;
    logic [DATA_WIDTH-1:0] rdata;
    logic rvalid;
    logic rready;

    modport master(
        input aclk, aresetn,
        output awaddr, wdata, wstrb, wvalid,
        input wready,
        output araddr, rready,
        input rdata, rvalid
    );

    modport slave(
        input aclk, aresetn,
        input awaddr, wdata, wstrb, wvalid,
        output wready,
        input araddr, rready,
        output rdata, rvalid
    );
endinterface

// Assertion checker module to be bound
module protocol_checker (
    input logic aclk,
    input logic aresetn,
    input logic [31:0] wdata,
    input logic [3:0] wstrb,
    input logic wvalid,
    input logic wready
);
    // Simple protocol check: wdata and wstrb must be stable when wvalid is high
    logic wvalid_d;
    logic [31:0] wdata_d;
    logic [3:0] wstrb_d;

    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            wvalid_d <= 0;
            wdata_d <= 0;
            wstrb_d <= 0;
        end else begin
            wvalid_d <= wvalid;
            wdata_d <= wdata;
            wstrb_d <= wstrb;
        end
    end

    // When wvalid was high and wready was low, wdata/wstrb should remain stable
    always_ff @(posedge aclk) begin
        if (aresetn && wvalid_d && !wready && wvalid) begin
            // In real assertion: assert(wdata == wdata_d);
            // Here just sample for testing
        end
    end
endmodule

// Driver BFM module (target of bind)
module axi4_driver_bfm (
    input logic aclk,
    input logic aresetn
);
    // Simple driver logic
    logic active;
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn)
            active <= 0;
        else
            active <= 1;
    end
endmodule

// Agent BFM that contains driver and bind statement (source of bind)
module axi4_agent_bfm (
    axi4_if.master intf  // Interface port from source module
);
    // Local signals
    wire aclk = intf.aclk;
    wire aresetn = intf.aresetn;

    // Driver instance (target of bind)
    axi4_driver_bfm driver_bfm (
        .aclk(aclk),
        .aresetn(aresetn)
    );

    // Bind statement: the expressions in port connections should be evaluated
    // in axi4_agent_bfm scope, so intf.wdata, intf.wstrb etc. should resolve here
    bind axi4_driver_bfm protocol_checker protocol_chk (
        .aclk(aclk),
        .aresetn(aresetn),
        .wdata(intf.wdata),      // Interface member access from source module
        .wstrb(intf.wstrb),      // Interface member access from source module
        .wvalid(intf.wvalid),    // Interface member access from source module
        .wready(intf.wready)     // Interface member access from source module
    );
endmodule

// Top-level test
module t (
    input clk
);
    logic aresetn;

    // Interface instance
    axi4_if #(.DATA_WIDTH(32)) axi (.aclk(clk), .aresetn(aresetn));

    // Agent BFM instance
    axi4_agent_bfm agent (.intf(axi));

    // Simple stimulus
    integer cnt = 0;

    always @(posedge clk) begin
        cnt <= cnt + 1;

        // Reset sequence
        if (cnt < 3) begin
            aresetn <= 0;
            axi.wdata <= 0;
            axi.wstrb <= 0;
            axi.wvalid <= 0;
        end else begin
            aresetn <= 1;
        end

        // Write transaction
        if (cnt == 5) begin
            axi.wdata <= 32'hDEADBEEF;
            axi.wstrb <= 4'hF;
            axi.wvalid <= 1;
        end

        if (cnt == 7) begin
            axi.wready <= 1;
        end

        if (cnt == 8) begin
            axi.wvalid <= 0;
            axi.wready <= 0;
        end

        // End test
        if (cnt > 15) begin
            $write("*-* All Finished *-*\n");
            $finish;
        end
    end
endmodule
