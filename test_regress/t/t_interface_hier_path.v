// DESCRIPTION: Verilator: Test interface port connection via hierarchical path
// This pattern is used in UVM VIPs where macros expand to interface paths
//
// This file is part of Verilator.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// Inner interface
interface inner_iface(input logic clk);
  logic [7:0] data;
  logic valid;

  modport master(output data, output valid);
  modport slave(input data, input valid);
endinterface

// Container interface that has inner interfaces
interface container_iface(input logic clk);
  inner_iface inner(.clk(clk));

  logic [7:0] other_data;
endinterface

// Module that takes an inner interface port
module uses_inner(inner_iface.master ifc);
  // Use initial block since we're just setting constant values
  initial begin
    ifc.data = 8'hAB;
    ifc.valid = 1;
  end
endmodule

// Top module demonstrating the pattern
module t;
  logic clk = 0;
  always #5 clk = ~clk;

  container_iface container(.clk(clk));

  // This is the pattern that needs to work:
  // Connecting an interface port using a hierarchical path
  uses_inner u_inner(.ifc(container.inner));

  // Check values after initial blocks have executed
  int cycle = 0;
  always @(posedge clk) begin
    cycle <= cycle + 1;
    if (cycle == 2) begin
      if (container.inner.data == 8'hAB && container.inner.valid == 1) begin
        $write("*-* All Finished *-*\n");
        $finish;
      end else begin
        $display("FAIL: data=%h valid=%b", container.inner.data, container.inner.valid);
        $stop;
      end
    end
  end
endmodule
