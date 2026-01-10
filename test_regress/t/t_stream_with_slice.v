// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024.
// SPDX-License-Identifier: CC0-1.0

// Test stream expressions with slice specification (with [])

module t;
   // Test 1: Simple slice - stream 32 bits in 8-bit chunks
   logic [31:0] data32;
   logic [7:0] bytes[4];

   // Test 2: Reverse streaming with slice
   logic [31:0] result;

   initial begin
      data32 = 32'hDEADBEEF;

      // Stream left with 8-bit slices: should produce {EF, BE, AD, DE}
      // {>> {data32 with [8]}} means: slice data32 into 8-bit chunks, stream left-to-right
      bytes = {>> {data32 with [8]}};

      // Verify
      if (bytes[0] !== 8'hEF) begin
         $display("FAIL: bytes[0] = %h, expected EF", bytes[0]);
         $stop;
      end
      if (bytes[1] !== 8'hBE) begin
         $display("FAIL: bytes[1] = %h, expected BE", bytes[1]);
         $stop;
      end
      if (bytes[2] !== 8'hAD) begin
         $display("FAIL: bytes[2] = %h, expected AD", bytes[2]);
         $stop;
      end
      if (bytes[3] !== 8'hDE) begin
         $display("FAIL: bytes[3] = %h, expected DE", bytes[3]);
         $stop;
      end

      // Test reverse: stream back to 32-bit
      result = {>> {bytes with [8]}};
      if (result !== 32'hDEADBEEF) begin
         $display("FAIL: result = %h, expected DEADBEEF", result);
         $stop;
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
