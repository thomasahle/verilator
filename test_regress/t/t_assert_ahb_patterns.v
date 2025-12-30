// DESCRIPTION: Verilator: Test for AHB-style SVA patterns
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test SVA patterns from AHB AVIP that were failing
// These patterns are inside an interface bound to a module

interface test_assertions (
   input logic clk,
   input logic resetn,
   input logic hwrite,
   input logic hready,
   input logic [1:0] htrans,
   input logic hselx,
   input logic [31:0] hwdata,
   input logic [2:0] hburst,
   input logic [31:0] haddr
);
   // Pattern 1: (expr) ##1 $stable(expr) |-> expr
   property checkHwdataValid;
      @(posedge clk) disable iff (!resetn)
      (hwrite && hready && (htrans != 2'b00) && hselx == 1) ##1 $stable(hready)|-> (!$isunknown(hwdata));
   endproperty
   assert property (checkHwdataValid) else $error("checkHwdataValid failed");

   // Pattern 2: expr |-> ##[1:$] expr
   property checkHtransValidity;
      @(posedge clk) disable iff (!resetn)
      (htrans == 2'b10 || htrans == 2'b11) |-> ##[1:$] hready;
   endproperty
   assert property (checkHtransValidity) else $error("checkHtransValidity failed");

   // Pattern 3: (complex_expr) ##1 (expr) && $stable(expr) |-> expr
   property checkBurstIncr;
      @(posedge clk) disable iff (!resetn)
      ((hburst inside {3'b011,3'b101,3'b111}) && (htrans == 2'b11 || htrans==2'b10))
       ##1 (htrans ==2'b11) && $stable(hburst) && !$stable(haddr) |-> (haddr > 0);
   endproperty
   assert property (checkBurstIncr) else $error("checkBurstIncr failed");

   // Pattern 4: (expr) ##1 hselx |-> expr
   property checkTransIdleToNonSeq;
      @(posedge clk) disable iff(!resetn) ((htrans == 2'b00) ##1 hselx) |-> ( htrans == 2'b10);
   endproperty
   assert property (checkTransIdleToNonSeq) else $error("checkTransIdleToNonSeq failed");
endinterface

// Target module for bind
module target_module(
   input logic clk,
   input logic resetn,
   input logic hwrite,
   input logic hready,
   input logic [1:0] htrans,
   input logic hselx,
   input logic [31:0] hwdata,
   input logic [2:0] hburst,
   input logic [31:0] haddr
);
endmodule

module t;
   logic clk = 0;
   always #5 clk = ~clk;

   int cyc = 0;
   logic resetn = 0;
   logic hwrite, hready, hselx;
   logic [1:0] htrans;
   logic [31:0] hwdata, haddr;
   logic [2:0] hburst;

   target_module tm(
      .clk(clk),
      .resetn(resetn),
      .hwrite(hwrite),
      .hready(hready),
      .htrans(htrans),
      .hselx(hselx),
      .hwdata(hwdata),
      .hburst(hburst),
      .haddr(haddr)
   );

   // Bind assertion interface to target module
   bind target_module test_assertions ta(
      .clk(clk),
      .resetn(resetn),
      .hwrite(hwrite),
      .hready(hready),
      .htrans(htrans),
      .hselx(hselx),
      .hwdata(hwdata),
      .hburst(hburst),
      .haddr(haddr)
   );

   always @(posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 2) resetn <= 1;
      hwrite <= 1;
      hready <= 1;
      htrans <= 2'b10;
      hselx <= 1;
      hwdata <= 32'h12345678;
      haddr <= 32'h100 + cyc * 4;
      hburst <= 3'b011;
      if (cyc >= 20) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
