// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test randomize() with (vars) { constraints } syntax
// IEEE 1800-2017 18.7

class Cls;
  rand int m_x;
  int m_y = 100;
endclass

// Test 1: randomize() with (var) and external variable in constraint
function int func1(Cls obj, int y);
  int result;
  result = obj.randomize() with (m_x) {
    m_x > 0;
    m_x < y;
  };
  return result;
endfunction

// Test 2: randomize() with (var) and member variable in constraint
function int func2(Cls obj);
  int result;
  result = obj.randomize() with (m_x) {
    m_x > 0;
    m_x < m_y;
  };
  return result;
endfunction

module t;
  initial begin
    Cls c;
    int result;
    c = new;

    // Test with y=10: m_x should be in range (0, 10)
    result = func1(c, 10);
    if (result == 0) $display("func1 failed to find solution");
    if (c.m_x <= 0 || c.m_x >= 10)
      $display("%%Error: func1 constraint violated: m_x=%0d", c.m_x);
    else
      $display("func1: m_x=%0d (0 < m_x < 10)", c.m_x);

    // Test with m_y=100: m_x should be in range (0, 100)
    result = func2(c);
    if (result == 0) $display("func2 failed to find solution");
    if (c.m_x <= 0 || c.m_x >= c.m_y)
      $display("%%Error: func2 constraint violated: m_x=%0d, m_y=%0d", c.m_x, c.m_y);
    else
      $display("func2: m_x=%0d (0 < m_x < %0d)", c.m_x, c.m_y);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
