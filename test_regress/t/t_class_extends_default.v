// DESCRIPTION: Verilator: Verilog Test module for extends with 'default'
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test IEEE 1800-2023 'extends (default)' and 'super.new(default)' features

class BaseClass;
  int base_value;
  string name;

  function new(int val = 100, string nm = "default_name");
    base_value = val;
    name = nm;
  endfunction
endclass

// Test 1: extends with (default) - uses parent's default constructor args
class ChildWithDefault extends BaseClass(default);
  int child_value;

  function new(int cv);
    child_value = cv;
  endfunction
endclass

// Test 2: Child without (default) but calls super.new with default
class ChildSuperDefault extends BaseClass;
  int child_value;

  function new(int cv);
    super.new(default);
    child_value = cv;
  endfunction
endclass

// Test 3: Child that provides explicit args (for comparison)
class ChildExplicit extends BaseClass;
  int child_value;

  function new(int cv);
    super.new(200, "explicit_name");
    child_value = cv;
  endfunction
endclass

// Test 4: No-argument parent constructor
class SimpleBase;
  int simple_val;

  function new();
    simple_val = 42;
  endfunction
endclass

class SimpleChild extends SimpleBase(default);
  function new();
  endfunction
endclass

module t;
  initial begin
    ChildWithDefault c1;
    ChildSuperDefault c2;
    ChildExplicit c3;
    SimpleChild c4;

    // Test ChildWithDefault - should use parent's defaults
    c1 = new(10);
    if (c1.base_value != 100) begin
      $display("FAIL: c1.base_value = %0d, expected 100", c1.base_value);
      $stop;
    end
    if (c1.name != "default_name") begin
      $display("FAIL: c1.name = %s, expected 'default_name'", c1.name);
      $stop;
    end
    if (c1.child_value != 10) begin
      $display("FAIL: c1.child_value = %0d, expected 10", c1.child_value);
      $stop;
    end

    // Test ChildSuperDefault - should also use parent's defaults
    c2 = new(20);
    if (c2.base_value != 100) begin
      $display("FAIL: c2.base_value = %0d, expected 100", c2.base_value);
      $stop;
    end
    if (c2.name != "default_name") begin
      $display("FAIL: c2.name = %s, expected 'default_name'", c2.name);
      $stop;
    end
    if (c2.child_value != 20) begin
      $display("FAIL: c2.child_value = %0d, expected 20", c2.child_value);
      $stop;
    end

    // Test ChildExplicit - should use explicit values
    c3 = new(30);
    if (c3.base_value != 200) begin
      $display("FAIL: c3.base_value = %0d, expected 200", c3.base_value);
      $stop;
    end
    if (c3.name != "explicit_name") begin
      $display("FAIL: c3.name = %s, expected 'explicit_name'", c3.name);
      $stop;
    end

    // Test SimpleChild
    c4 = new();
    if (c4.simple_val != 42) begin
      $display("FAIL: c4.simple_val = %0d, expected 42", c4.simple_val);
      $stop;
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
