// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024.
// SPDX-License-Identifier: CC0-1.0

// Test stream expressions with selection (with [])
// IEEE 1800-2017 section 11.4.14.2:
// "If an array_range_expression is specified for a stream_expression,
//  then only that array element or slice is streamed."

module t;
   // Test 1: with[] on unpacked array - select element
   logic [7:0] arr[4];
   logic [7:0] elem_result;

   // Test 2: with[] on packed value - select bit range
   logic [31:0] data32;
   logic [7:0] slice_result;

   initial begin
      // Initialize array
      arr[0] = 8'hAA;
      arr[1] = 8'hBB;
      arr[2] = 8'hCC;
      arr[3] = 8'hDD;

      // Test 1: Stream single array element with with[n]
      // This should stream only arr[1], which is 8'hBB
      elem_result = {>> {arr with [1]}};
      if (elem_result !== 8'hBB) begin
         $display("FAIL: elem_result = %h, expected BB", elem_result);
         $stop;
      end

      // Test 2: Stream packed bit range with with[a:b]
      data32 = 32'hDEADBEEF;
      // Stream bits 15:8 (which is 8'hBE)
      slice_result = {>> {data32 with [15:8]}};
      if (slice_result !== 8'hBE) begin
         $display("FAIL: slice_result = %h, expected BE", slice_result);
         $stop;
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
