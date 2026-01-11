// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test for stream expression with[] bit slice selection on packed arrays
// IEEE 1800-2017 Section 11.4.14.2

module t;

   // Test data - packed arrays for bit selection
   logic [31:0] data;
   logic [31:0] result;
   logic [15:0] result16;
   logic [7:0] result8;
   logic [3:0] result4;
   logic result1;

   initial begin
      data = 32'hDEADBEEF;

      // Test 1: Stream with single bit selection using with[]
      result1 = {<< 1 {data with [7]}};  // Select bit 7, stream it
      // Bit 7 of 0xEF = 1
      if (result1 !== 1'b1) begin
         $display("Test 1 FAILED: Expected 1, got %b", result1);
         $stop;
      end

      // Test 2: Stream with bit range selection using with[]
      result16 = {<< 4 {data with [15:0]}};  // Select lower 16 bits, reverse nibbles
      // 0xBEEF nibble-reversed = 0xFEEB
      if (result16 !== 16'hFEEB) begin
         $display("Test 2 FAILED: Expected 0xFEEB, got 0x%h", result16);
         $stop;
      end

      // Test 3: Stream with ascending part select using with[]
      result16 = {<< 4 {data with [0 +: 16]}};  // Select bits [15:0] via +: notation
      // 0xBEEF nibble-reversed = 0xFEEB
      if (result16 !== 16'hFEEB) begin
         $display("Test 3 FAILED: Expected 0xFEEB, got 0x%h", result16);
         $stop;
      end

      // Test 4: Stream with descending part select using with[]
      result16 = {<< 4 {data with [31 -: 16]}};  // Select bits [31:16] via -: notation
      // 0xDEAD nibble-reversed = 0xDAED
      if (result16 !== 16'hDAED) begin
         $display("Test 4 FAILED: Expected 0xDAED, got 0x%h", result16);
         $stop;
      end

      // Test 5: Right stream with bit selection (no reversal)
      result16 = {>> 4 {data with [15:0]}};  // Select lower 16 bits, no nibble reverse
      if (result16 !== 16'hBEEF) begin
         $display("Test 5 FAILED: Expected 0xBEEF, got 0x%h", result16);
         $stop;
      end

      // Test 6: Stream with byte slice
      data = 32'h12345678;
      result8 = {<< 4 {data with [7:0]}};  // Select byte 0, reverse nibbles
      // 0x78 nibble-reversed = 0x87
      if (result8 !== 8'h87) begin
         $display("Test 6 FAILED: Expected 0x87, got 0x%h", result8);
         $stop;
      end

      $display("All tests passed!");
      $write("*-* All Coverage *-*\n");
      $finish;
   end

endmodule
