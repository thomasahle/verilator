// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

  // Test dynamic arrays
  logic [7:0] dyn8[];
  logic [15:0] dyn16[];

  // Test queues
  logic [7:0] q8[$];
  int q_int[$];

  initial begin
    // Empty collections should have 0 bits
    if ($bits(dyn8) != 0) $stop;
    if ($bits(q8) != 0) $stop;

    // Test dynamic array with elements
    dyn8 = new[3];
    if ($bits(dyn8) != 24) $stop;  // 8 bits * 3 elements = 24

    dyn16 = new[5];
    if ($bits(dyn16) != 80) $stop;  // 16 bits * 5 elements = 80

    // Test queue with elements
    q8.push_back(8'hAA);
    q8.push_back(8'hBB);
    if ($bits(q8) != 16) $stop;  // 8 bits * 2 elements = 16

    q_int.push_back(100);
    q_int.push_back(200);
    q_int.push_back(300);
    if ($bits(q_int) != 96) $stop;  // 32 bits * 3 elements = 96

    // Test resizing
    dyn8 = new[10];
    if ($bits(dyn8) != 80) $stop;  // 8 bits * 10 elements = 80

    // Test clear
    q8.delete();
    if ($bits(q8) != 0) $stop;  // Empty queue = 0 bits

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
