// DESCRIPTION: Verilator: Verilog Test module for randomize(null)
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test randomize(null) functionality per IEEE 1800-2017 18.7

class MyClass;
  rand int value;
  int non_rand_value;

  function new();
    value = 0;
    non_rand_value = 42;
  endfunction

  constraint c1 { value >= 0; value < 100; }
endclass

module t;
  initial begin
    MyClass obj;
    int result;
    int orig_value;

    obj = new();
    obj.value = 50;
    orig_value = obj.value;

    // randomize(null) should:
    // 1. NOT randomize any rand variables
    // 2. Return 1 (success) since no constraints to violate
    result = obj.randomize(null);

    // Value should be unchanged
    if (obj.value != orig_value) begin
      $display("FAIL: randomize(null) changed value from %0d to %0d", orig_value, obj.value);
      $stop;
    end

    // Result should be 1 (success)
    if (result != 1) begin
      $display("FAIL: randomize(null) returned %0d, expected 1", result);
      $stop;
    end

    // non_rand_value should also be unchanged
    if (obj.non_rand_value != 42) begin
      $display("FAIL: non_rand_value changed");
      $stop;
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
