// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test randomize(vars) with { constraints } - IEEE 1800-2017 18.7
// Randomize specific variables with additional inline constraints

class Packet;
   rand bit [7:0] addr;
   rand bit [7:0] data;
   rand bit [3:0] len;

   constraint c_len { len inside {[1:8]}; }
endclass

module t;
   Packet pkt;

   initial begin
      pkt = new;

      // Test 1: randomize(addr) with constraint - only randomize addr
      pkt.addr = 8'hFF;
      pkt.data = 8'hAA;
      pkt.len = 4'd5;

      // Randomize only addr with constraint that addr > 0
      // data and len should remain unchanged (treated as state)
      void'(pkt.randomize(addr) with { addr > 8'h10; });

      if (pkt.addr <= 8'h10) begin
         $display("FAIL: addr should be > 0x10, got %h", pkt.addr);
         $stop;
      end
      if (pkt.data !== 8'hAA) begin
         $display("FAIL: data should be unchanged (0xAA), got %h", pkt.data);
         $stop;
      end
      if (pkt.len !== 4'd5) begin
         $display("FAIL: len should be unchanged (5), got %d", pkt.len);
         $stop;
      end
      $display("Test 1 passed: addr=%h, data=%h, len=%d", pkt.addr, pkt.data, pkt.len);

      // Test 2: randomize(addr, data) with constraint
      pkt.len = 4'd7;
      void'(pkt.randomize(addr, data) with {
         addr < 8'h80;
         data > 8'h20;
      });

      if (pkt.addr >= 8'h80) begin
         $display("FAIL: addr should be < 0x80, got %h", pkt.addr);
         $stop;
      end
      if (pkt.data <= 8'h20) begin
         $display("FAIL: data should be > 0x20, got %h", pkt.data);
         $stop;
      end
      if (pkt.len !== 4'd7) begin
         $display("FAIL: len should be unchanged (7), got %d", pkt.len);
         $stop;
      end
      $display("Test 2 passed: addr=%h, data=%h, len=%d", pkt.addr, pkt.data, pkt.len);

      // Test 3: randomize all with inline constraint (existing feature)
      void'(pkt.randomize() with { addr == 8'h55; data == 8'hAA; });
      if (pkt.addr !== 8'h55 || pkt.data !== 8'hAA) begin
         $display("FAIL: randomize() with constraint failed");
         $stop;
      end
      $display("Test 3 passed: addr=%h, data=%h, len=%d", pkt.addr, pkt.data, pkt.len);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
