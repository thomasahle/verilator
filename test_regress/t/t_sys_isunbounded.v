// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   // Test $isunbounded system function
   int q[$];                    // Unbounded queue
   int q_bounded[$:100];        // Bounded queue with limit 100
   int arr[];                   // Dynamic array
   int fixed_arr[10];           // Fixed array

   initial begin
      // Unbounded queue - $isunbounded should return 1
      if ($isunbounded(q) != 1) $stop;

      // Bounded queue - $isunbounded should return 0
      if ($isunbounded(q_bounded) != 0) $stop;

      // Dynamic array - not a queue, $isunbounded returns 0
      if ($isunbounded(arr) != 0) $stop;

      // Fixed array - not a queue, $isunbounded returns 0
      if ($isunbounded(fixed_arr) != 0) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
