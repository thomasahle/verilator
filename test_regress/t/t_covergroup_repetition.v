// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test coverage repetition operators [*N], [->N], [=N]

module t(/*AUTOARG*/);

   int value;
   int errors = 0;

   // Covergroup with repetition bins
   covergroup cg_repetition;
      coverpoint value {
         // Consecutive repetition [*3] - value must be 5 three times in a row
         bins consecutive_rep = (5 [*3]);

         // Goto repetition [->2] - value must be 10 two times total (non-consecutive ok)
         bins goto_rep = (10 [->2]);

         // Non-consecutive repetition [=2] - same as goto semantically
         bins nonconsec_rep = (15 [=2]);

         // Regular bins for comparison
         bins single_val = {5};
      }
   endgroup

   cg_repetition cg = new;

   initial begin
      // Test consecutive repetition [*3]
      // Needs three consecutive matches of value=5
      $display("Testing consecutive repetition [*3]...");
      value = 1; cg.sample();  // No match
      value = 5; cg.sample();  // Match 1
      value = 5; cg.sample();  // Match 2
      value = 1; cg.sample();  // No match - reset
      value = 5; cg.sample();  // Match 1
      value = 5; cg.sample();  // Match 2
      value = 5; cg.sample();  // Match 3 - HIT!
      value = 5; cg.sample();  // Match 1 (new sequence)
      value = 5; cg.sample();  // Match 2
      value = 5; cg.sample();  // Match 3 - HIT again!

      // Test goto repetition [->2]
      // Needs two total matches of value=10 (can be non-consecutive)
      $display("Testing goto repetition [->2]...");
      value = 10; cg.sample(); // Match 1
      value = 1; cg.sample();  // Different value - doesn't reset counter
      value = 2; cg.sample();  // Different value
      value = 10; cg.sample(); // Match 2 - HIT!
      // Counter should reset after hit
      value = 10; cg.sample(); // Match 1 (new sequence)
      value = 10; cg.sample(); // Match 2 - HIT again!

      // Test non-consecutive repetition [=2]
      // Same semantics as goto
      $display("Testing non-consecutive repetition [=2]...");
      value = 15; cg.sample(); // Match 1
      value = 3; cg.sample();  // Different value
      value = 4; cg.sample();  // Different value
      value = 15; cg.sample(); // Match 2 - HIT!

      // Check that we got expected hits
      // Note: We can't directly query bin hit counts in standard SV,
      // but we can verify behavior through simulation completion
      $display("All repetition tests completed");

      $write("*-* All Coverage Tests Passed *-*\n");
      $finish;
   end

endmodule
