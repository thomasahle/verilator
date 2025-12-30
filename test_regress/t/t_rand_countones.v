// DESCRIPTION: Verilator: Test $countones in randomization constraints
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test that $countones works correctly in inline randomization constraints

module t;
  class TestClass;
    rand bit [7:0] data;
    rand bit [3:0] nibble;
    rand bit single;
    rand bit [0:0] single_vec;

    // Test basic $countones constraint
    function bit test_countones_basic();
      int pass = 1;
      // $countones should select exactly 3 bits set
      if (!randomize() with { $countones(data) == 3; }) begin
        $display("[FAIL] randomize with $countones(data)==3 failed");
        return 0;
      end
      if ($countones(data) != 3) begin
        $display("[FAIL] $countones(data) = %0d, expected 3, data = %b", $countones(data), data);
        return 0;
      end
      $display("[PASS] $countones(data)==3: data=%b, countones=%0d", data, $countones(data));
      return 1;
    endfunction

    // Test $countones == 0 (all zeros)
    function bit test_countones_zero();
      if (!randomize() with { $countones(nibble) == 0; }) begin
        $display("[FAIL] randomize with $countones(nibble)==0 failed");
        return 0;
      end
      if (nibble != 0) begin
        $display("[FAIL] nibble should be 0, got %b", nibble);
        return 0;
      end
      $display("[PASS] $countones(nibble)==0: nibble=%b", nibble);
      return 1;
    endfunction

    // Test $countones on 1-bit variable (this is the SPI AVIP pattern)
    function bit test_countones_single_bit();
      // This is the exact pattern from SPI AVIP:
      // $countones(req.cs) == NO_OF_SLAVES - 1 where cs is 1-bit and NO_OF_SLAVES=1
      // So: $countones(single) == 0
      if (!randomize() with { $countones(single) == 0; }) begin
        $display("[FAIL] randomize with $countones(single)==0 failed");
        return 0;
      end
      if (single != 0) begin
        $display("[FAIL] single should be 0, got %b", single);
        return 0;
      end
      $display("[PASS] $countones(single)==0: single=%b", single);
      return 1;
    endfunction

    // Test combined constraint like SPI: $countones(cs) == 0 && cs[0] == 0
    function bit test_countones_combined();
      if (!randomize() with { $countones(single_vec) == 0; single_vec[0] == 0; }) begin
        $display("[FAIL] randomize with combined constraint failed");
        return 0;
      end
      if (single_vec != 0) begin
        $display("[FAIL] single_vec should be 0, got %b", single_vec);
        return 0;
      end
      $display("[PASS] combined constraint: single_vec=%b", single_vec);
      return 1;
    endfunction

    // Test $countones with constraint value from expression
    function bit test_countones_expression();
      int target = 2;
      if (!randomize() with { $countones(nibble) == target; }) begin
        $display("[FAIL] randomize with $countones(nibble)==target failed");
        return 0;
      end
      if ($countones(nibble) != target) begin
        $display("[FAIL] $countones(nibble) = %0d, expected %0d", $countones(nibble), target);
        return 0;
      end
      $display("[PASS] $countones(nibble)==%0d: nibble=%b", target, nibble);
      return 1;
    endfunction
  endclass

  initial begin
    TestClass tc = new;
    int pass = 1;

    pass &= tc.test_countones_basic();
    pass &= tc.test_countones_zero();
    pass &= tc.test_countones_single_bit();
    pass &= tc.test_countones_combined();
    pass &= tc.test_countones_expression();

    if (pass)
      $display("*-* All Coverage Tests Passed *-*");
    else
      $display("[FAIL] Some tests failed");
    $finish;
  end
endmodule
