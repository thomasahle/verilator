// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

// Test inout parameter in task with fork/join_none + disable fork pattern.
// This pattern is common in UVM AVIPs (e.g., I3C AVIP).
// The key is that the caller synchronizes with the forked process via
// wait + disable fork, so the inout variable is still valid when written.

typedef struct {
  bit [7:0] data;
  bit [7:0] addr;
  int count;
} transfer_s;

interface test_if(input logic clk);
  logic [7:0] bus_data;
  logic stop_cond;

  // Task with inout struct, fork/join_none, wait, disable fork pattern
  task sample_data_with_wait(inout transfer_s pkt);
    fork
      begin
        @(posedge clk);
        pkt.data = bus_data;
        pkt.count = pkt.count + 1;
      end
    join_none

    // Wait for stop condition, then disable fork (synchronization)
    wait(stop_cond);
    disable fork;
  endtask
endinterface

module t;
  logic clk = 0;
  always #5 clk = ~clk;

  test_if tif(.clk(clk));

  initial begin
    transfer_s xfer;
    xfer.data = 8'h55;
    xfer.addr = 8'h00;
    xfer.count = 0;

    tif.bus_data = 8'hAA;
    tif.stop_cond = 0;

    // Start background process that will signal stop
    fork
      begin
        #20;
        tif.stop_cond = 1;
      end
    join_none

    #10;  // Let fork start
    tif.sample_data_with_wait(xfer);

    $display("After sample with disable fork: data=%h, count=%d", xfer.data, xfer.count);

    if (xfer.data == 8'hAA && xfer.count == 1) begin
      $write("*-* All Finished *-*\n");
    end else begin
      $display("ERROR: Expected data=AA, count=1, got data=%h, count=%d", xfer.data, xfer.count);
      $stop;
    end

    $finish;
  end
endmodule
