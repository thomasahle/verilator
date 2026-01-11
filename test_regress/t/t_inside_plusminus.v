// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test for value_range with +/- and +%- syntax
// IEEE 1800-2017 Section 11.4.13

module t;

   int value;
   bit result;

   initial begin
      // Test 1: +/- range - [10 +/- 2] should match 8, 9, 10, 11, 12
      value = 10;
      result = value inside {[10 +/- 2]};  // 10 is in [8:12]
      if (!result) begin
         $display("Test 1a FAILED: 10 should be inside [10 +/- 2]");
         $stop;
      end

      value = 8;
      result = value inside {[10 +/- 2]};  // 8 is in [8:12]
      if (!result) begin
         $display("Test 1b FAILED: 8 should be inside [10 +/- 2]");
         $stop;
      end

      value = 12;
      result = value inside {[10 +/- 2]};  // 12 is in [8:12]
      if (!result) begin
         $display("Test 1c FAILED: 12 should be inside [10 +/- 2]");
         $stop;
      end

      value = 7;
      result = value inside {[10 +/- 2]};  // 7 is NOT in [8:12]
      if (result) begin
         $display("Test 1d FAILED: 7 should NOT be inside [10 +/- 2]");
         $stop;
      end

      value = 13;
      result = value inside {[10 +/- 2]};  // 13 is NOT in [8:12]
      if (result) begin
         $display("Test 1e FAILED: 13 should NOT be inside [10 +/- 2]");
         $stop;
      end

      // Test 2: +%- range - [100 +%- 10] should match 90 to 110
      // low = 100 * (100-10) / 100 = 90
      // high = 100 * (100+10) / 100 = 110
      value = 100;
      result = value inside {[100 +%- 10]};  // 100 is in [90:110]
      if (!result) begin
         $display("Test 2a FAILED: 100 should be inside [100 +%%- 10]");
         $stop;
      end

      value = 90;
      result = value inside {[100 +%- 10]};  // 90 is in [90:110]
      if (!result) begin
         $display("Test 2b FAILED: 90 should be inside [100 +%%- 10]");
         $stop;
      end

      value = 110;
      result = value inside {[100 +%- 10]};  // 110 is in [90:110]
      if (!result) begin
         $display("Test 2c FAILED: 110 should be inside [100 +%%- 10]");
         $stop;
      end

      value = 89;
      result = value inside {[100 +%- 10]};  // 89 is NOT in [90:110]
      if (result) begin
         $display("Test 2d FAILED: 89 should NOT be inside [100 +%%- 10]");
         $stop;
      end

      value = 111;
      result = value inside {[100 +%- 10]};  // 111 is NOT in [90:110]
      if (result) begin
         $display("Test 2e FAILED: 111 should NOT be inside [100 +%%- 10]");
         $stop;
      end

      // Test 3: +/- with variable bounds
      value = 50;
      result = value inside {[50 +/- 5]};
      if (!result) begin
         $display("Test 3 FAILED: 50 should be inside [50 +/- 5]");
         $stop;
      end

      $display("All tests passed!");
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
