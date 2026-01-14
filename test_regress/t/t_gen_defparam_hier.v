// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test hierarchical defparam with multiple dots

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   wire [31:0] o2, o3, o4;

   m1 m1a(.o2(o2), .o3(o3), .o4(o4));

   always @ (posedge clk) begin
      if (o2 != 8) $stop;
      if (o3 != 80) $stop;
      if (o4 != 400) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

module m1 (output wire [31:0] o2,
           output wire [31:0] o3,
           output wire [31:0] o4);
   m2 m2 (.*);
   // Simple defparam (already supported)
   defparam m2.PAR2 = 8;
   // Hierarchical defparam - 3 components (cell.cell.param)
   defparam m2.m3.PAR3 = 80;
   // Hierarchical defparam - 4 components (cell.cell.cell.param)
   defparam m2.m3.m4.PAR4 = 400;
endmodule

module m2 (output wire [31:0] o2,
           output wire [31:0] o3,
           output wire [31:0] o4);
   parameter PAR2 = 20;
   assign o2 = PAR2;
   m3 m3 (.*);
endmodule

module m3 (output wire [31:0] o3,
           output wire [31:0] o4);
   parameter PAR3 = 30;
   assign o3 = PAR3;
   m4 m4 (.*);
endmodule

module m4 (output wire [31:0] o4);
   parameter PAR4 = 40;
   assign o4 = PAR4;
endmodule
