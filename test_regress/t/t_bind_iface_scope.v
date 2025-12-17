// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test bind with interface port from source scope (IEEE 1800-2017 23.11)
// The expressions in a bind instantiation shall be evaluated in the scope
// where the bind construct appears.

interface SimpleIf(input logic clk);
   logic [7:0] data;
endinterface

module checker_mod(input logic clk, input logic [7:0] data);
   // Checker module that receives signals from bind source scope
endmodule

module target_mod();
   // Target module has no ports - bind will inject signals from source scope
endmodule

module source_mod(SimpleIf sif);
   // Source module has interface port
   target_mod target();

   // Bind with interface signals from source scope
   // Per IEEE 1800-2017 23.11: "sif.clk" and "sif.data" resolve in source_mod's scope
   bind target_mod checker_mod check_inst(.clk(sif.clk), .data(sif.data));
endmodule

module t;
   logic clk = 0;

   SimpleIf intf(.clk(clk));
   source_mod src(intf);

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
