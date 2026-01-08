// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test array 'map' method (IEEE 1800-2023 7.12.5)

module t;
   int dyn_arr[];
   int queue_q[$];
   int result_q[$];
   int fixed_arr[4];

   initial begin
      // Test with dynamic array
      dyn_arr = new[4];
      dyn_arr[0] = 1;
      dyn_arr[1] = 2;
      dyn_arr[2] = 3;
      dyn_arr[3] = 4;

      // Map: double each element
      result_q = dyn_arr.map(x) with (x * 2);
      if (result_q.size() != 4) $stop;
      if (result_q[0] != 2) $stop;
      if (result_q[1] != 4) $stop;
      if (result_q[2] != 6) $stop;
      if (result_q[3] != 8) $stop;

      // Map: square each element
      result_q = dyn_arr.map(x) with (x * x);
      if (result_q.size() != 4) $stop;
      if (result_q[0] != 1) $stop;
      if (result_q[1] != 4) $stop;
      if (result_q[2] != 9) $stop;
      if (result_q[3] != 16) $stop;

      // Test with queue
      queue_q.push_back(10);
      queue_q.push_back(20);
      queue_q.push_back(30);

      // Map: add 5 to each
      result_q = queue_q.map(x) with (x + 5);
      if (result_q.size() != 3) $stop;
      if (result_q[0] != 15) $stop;
      if (result_q[1] != 25) $stop;
      if (result_q[2] != 35) $stop;

      // Test with fixed-size array
      fixed_arr[0] = 100;
      fixed_arr[1] = 200;
      fixed_arr[2] = 300;
      fixed_arr[3] = 400;

      // Map: divide by 10
      result_q = fixed_arr.map(x) with (x / 10);
      if (result_q.size() != 4) $stop;
      if (result_q[0] != 10) $stop;
      if (result_q[1] != 20) $stop;
      if (result_q[2] != 30) $stop;
      if (result_q[3] != 40) $stop;

      // Test map with index access
      result_q = dyn_arr.map(x) with (x + dyn_arr[0]);
      if (result_q.size() != 4) $stop;
      if (result_q[0] != 2) $stop;  // 1 + 1
      if (result_q[1] != 3) $stop;  // 2 + 1
      if (result_q[2] != 4) $stop;  // 3 + 1
      if (result_q[3] != 5) $stop;  // 4 + 1

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
