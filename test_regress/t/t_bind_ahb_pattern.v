// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Thomas Ahle.
// SPDX-License-Identifier: CC0-1.0

// Test AHB-style bind pattern with interface port from source scope

interface AhbInterface(input logic hclk, input logic hresetn);
   logic [31:0] haddr;
   logic [31:0] hwdata;
   logic [31:0] hrdata;
   logic        hwrite;
   logic        hready;
endinterface

module AhbMasterAssertion(
   input logic hclk,
   input logic hresetn,
   input logic [31:0] haddr,
   input logic [31:0] hwdata,
   input logic [31:0] hrdata,
   input logic hwrite,
   input logic hready
);
   // Assertion module receives signals from bind source scope
   property p_valid_write;
      @(posedge hclk) disable iff (!hresetn)
      hwrite && hready |-> !$isunknown(hwdata);
   endproperty
   assert property (p_valid_write);
endmodule

module AhbMasterMonitorBFM(AhbInterface ahbIf);
   // Monitor BFM - target of bind
endmodule

module AhbMasterDriverBFM(AhbInterface ahbIf);
   // Driver BFM
endmodule

module AhbMasterAgentBFM(AhbInterface ahbInterface);
   // Agent BFM instantiates monitor and driver
   AhbMasterMonitorBFM monitorBfm(.ahbIf(ahbInterface));
   AhbMasterDriverBFM driverBfm(.ahbIf(ahbInterface));

   // Bind assertion to monitor with signals from ahbInterface (source scope)
   // Per IEEE 1800-2017 23.11: ahbInterface.* resolved in AhbMasterAgentBFM scope
   bind AhbMasterMonitorBFM AhbMasterAssertion ahb_assert (
      .hclk(ahbInterface.hclk),
      .hresetn(ahbInterface.hresetn),
      .haddr(ahbInterface.haddr),
      .hwdata(ahbInterface.hwdata),
      .hrdata(ahbInterface.hrdata),
      .hwrite(ahbInterface.hwrite),
      .hready(ahbInterface.hready)
   );
endmodule

module t;
   logic clk = 0;
   logic resetn = 1;

   AhbInterface ahbIf(.hclk(clk), .hresetn(resetn));
   AhbMasterAgentBFM agent(.ahbInterface(ahbIf));

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
