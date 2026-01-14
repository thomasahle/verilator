// DESCRIPTION: Verilator: Test bind statement inside a module (not at top level)
//
// Tests that bind statements work correctly when placed inside a module
// that is instantiated multiple times via generate.
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Simple interface to bind into
interface my_driver_bfm(input logic clk, input logic rst_n);
   // Variables that would trigger "Duplicate declaration" if bind is broken
   reg [7:0] counter = 0;
   reg [7:0] data = 0;
   string name = "MY_DRIVER_BFM";

   initial begin
      $display("Driver BFM initialized");
   end
endinterface

// Simple module to bind
module my_assertions(input logic clk, input logic rst_n);
   initial begin
      $display("Assertions bound");
   end
endmodule

// Agent BFM module that contains the bind statement
module my_agent_bfm #(parameter int AGENT_ID = 0)(input logic clk, input logic rst_n);
   // Instantiate driver BFM
   my_driver_bfm drv_bfm(.clk(clk), .rst_n(rst_n));

   // Bind assertions to the driver BFM - this is inside a module, not at top level
   bind my_driver_bfm my_assertions assertions_inst(.clk(clk), .rst_n(rst_n));

   initial begin
      $display("Agent BFM %0d initialized", AGENT_ID);
   end
endmodule

// Top level with generate loop
module t;
   logic clk = 0;
   logic rst_n = 0;

   always #5 clk = ~clk;

   initial begin
      rst_n = 0;
      #20 rst_n = 1;
   end

   // Generate multiple agents - tests bind inside module with generate
   genvar i;
   generate
      for (i = 0; i < 2; i++) begin : agents
         my_agent_bfm #(.AGENT_ID(i)) agent(.clk(clk), .rst_n(rst_n));
      end
   endgenerate

   initial begin
      #100;
      $display("[PASS] Bind inside module with generate loop works");
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
