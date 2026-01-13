// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test foreach with struct-keyed associative array and member access on key

typedef struct packed {
   logic [31:0] min;
   logic [31:0] max;
} addr_range_t;

module t(/*AUTOARG*/);

   addr_range_t key1;
   addr_range_t key2;
   int arr[addr_range_t];

   initial begin
      key1 = '{min: 0, max: 100};
      key2 = '{min: 200, max: 300};

      arr[key1] = 1;
      arr[key2] = 2;

      // Test foreach with member access on struct key
      foreach (arr[range]) begin
         $display("range: min=%0d, max=%0d, value=%0d", range.min, range.max, arr[range]);
         if (range.min == 0) begin
            if (range.max != 100) $stop;
            if (arr[range] != 1) $stop;
         end else if (range.min == 200) begin
            if (range.max != 300) $stop;
            if (arr[range] != 2) $stop;
         end else begin
            $stop;
         end
      end

      $write("*-* All Coverage *-*\n");
      $finish;
   end
endmodule
