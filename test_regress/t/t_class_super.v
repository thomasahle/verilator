// DESCRIPTION: Verilator: Verilog Test module for super keyword
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test the 'super' keyword for calling parent class methods

class Base;
  int value;

  function new();
    value = 10;
  endfunction

  virtual function int get_value();
    return value;
  endfunction

  virtual function void set_value(int v);
    value = v;
  endfunction

  virtual function int add_value(int v);
    return value + v;
  endfunction
endclass

class Child extends Base;
  int child_value;

  function new();
    super.new();  // Call parent constructor
    child_value = 20;
  endfunction

  virtual function int get_value();
    // Override but also call parent
    return super.get_value() + child_value;
  endfunction

  virtual function void set_value(int v);
    super.set_value(v);  // Call parent method
    child_value = v * 2;
  endfunction

  // Access parent method from different context
  function int get_base_value();
    return super.get_value();
  endfunction
endclass

class GrandChild extends Child;
  function new();
    super.new();  // Call parent constructor
  endfunction

  virtual function int get_value();
    // Override calling grandparent through parent
    return super.get_value() + 5;
  endfunction
endclass

module t;
  initial begin
    Base b;
    Child c;
    GrandChild gc;

    // Test basic inheritance
    b = new();
    if (b.get_value() != 10) $stop;

    // Test super.new() and super.method()
    c = new();
    if (c.value != 10) $stop;           // Parent value set by super.new()
    if (c.child_value != 20) $stop;     // Child value set
    if (c.get_value() != 30) $stop;     // 10 + 20 from override calling super
    if (c.get_base_value() != 10) $stop; // Direct super call

    // Test super.set_value()
    c.set_value(5);
    if (c.value != 5) $stop;            // Parent value updated
    if (c.child_value != 10) $stop;     // Child value is v*2

    // Test chained inheritance
    gc = new();
    if (gc.get_value() != 35) $stop;    // (10 + 20) + 5 from grandchild override

    $write("*-* All Super Tests Passed\n");
    $finish;
  end
endmodule
