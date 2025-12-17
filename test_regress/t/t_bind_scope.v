// DESCRIPTION: Verilator: Verilog Test module for bind scope resolution
// Test IEEE 1800-2017 section 23.11: bind expressions evaluated in bind source scope
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test that bind statements can reference variables from the bind source scope
// This tests both simple variables and interface member access

// Simple AXI-like interface
interface axi_if(input logic clk);
  logic [31:0] wdata;
  logic [31:0] rdata;
  logic valid;
  logic ready;

  modport master(input clk, output wdata, valid, input rdata, ready);
  modport slave(input clk, input wdata, valid, output rdata, ready);
endinterface

// Check interface - to be bound
interface check_if(input logic clk, input logic [31:0] data, input logic signal);
  always_ff @(posedge clk) begin
    // Simple check
  end
endinterface

// Module that we bind into (target)
module target_module(input logic clk, input logic [31:0] in_data);
  // Target module content - no access to source module's intf
  logic internal;
  always_ff @(posedge clk) internal <= in_data[0];
endmodule

// Source module where bind statement is written
module source_module(input logic clk, axi_if.master intf);
  // Local variable in source module
  logic [31:0] local_data;
  assign local_data = intf.wdata;

  // Target module instance
  target_module target_inst(.clk(clk), .in_data(intf.wdata));

  // Bind statement - per IEEE 1800-2017 section 23.11, the expressions
  // in the port connection list should be evaluated in the scope where
  // the bind statement appears (source_module), not where it's bound to
  // (target_module)
  bind target_module check_if checker_inst (
    .clk(clk),
    .data(local_data),    // Local variable from source module
    .signal(intf.valid)   // Interface member from source module
  );
endmodule

// Top-level test
module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   // Create the interface
   axi_if axi(.clk(clk));

   // Simple stimulus
   integer cnt = 0;

   source_module src(.clk(clk), .intf(axi));

   always @(posedge clk) begin
     cnt <= cnt + 1;
     axi.wdata <= cnt;
     axi.valid <= (cnt > 2);
     if (cnt > 10) begin
       $write("*-* All Finished *-*\n");
       $finish;
     end
   end
endmodule
