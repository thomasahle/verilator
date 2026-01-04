// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test coverage tolerance ranges [value +/- tol] and [value +%- pct]

module t(/*AUTOARG*/);

   int value;
   int errors = 0;

   // Covergroup with tolerance bins
   covergroup cg_tolerance;
      coverpoint value {
         // Absolute tolerance: [100 +/- 10] means values 90-110
         bins abs_tol = {[100 +/- 10]};

         // Percentage tolerance: [200 +%- 25.0] means 150-250 (200 * 0.75 to 200 * 1.25)
         bins pct_tol = {[200 +%- 25.0]};

         // Regular bins for comparison
         bins exact_val = {50};
      }
   endgroup

   cg_tolerance cg = new;

   initial begin
      // Test absolute tolerance [100 +/- 10]
      $display("Testing absolute tolerance [100 +/- 10]...");
      value = 89; cg.sample();   // Out of range (should not hit)
      value = 90; cg.sample();   // In range (should hit)
      value = 100; cg.sample();  // In range (center)
      value = 110; cg.sample();  // In range (upper bound)
      value = 111; cg.sample();  // Out of range (should not hit)

      // Test percentage tolerance [200 +%- 25.0]
      $display("Testing percentage tolerance [200 +%%- 25.0]...");
      value = 149; cg.sample();  // Out of range (should not hit)
      value = 150; cg.sample();  // In range (lower bound)
      value = 200; cg.sample();  // In range (center)
      value = 250; cg.sample();  // In range (upper bound)
      value = 251; cg.sample();  // Out of range (should not hit)

      // Test exact value for comparison
      $display("Testing exact value 50...");
      value = 50; cg.sample();

      $display("All tolerance tests completed");
      $write("*-* All Coverage Tests Passed *-*\n");
      $finish;
   end

endmodule
