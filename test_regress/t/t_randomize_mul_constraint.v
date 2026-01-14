// DESCRIPTION: Verilator: Test multiplication in constraints
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0
//
// Tests that signed multiplication works in randomization constraints

class MultTest;
  rand int a, b, c;
  constraint c_simple { a > 0; a < 100; }
  constraint c_double { b == a * 2; }
  constraint c_triple { c == a * 3; }
endclass

class MultTestTwo;
  rand int x, y, z;
  constraint c_mult { z == x * y; }
  constraint c_range { x > 0; x < 10; y > 0; y < 10; }
endclass

module t;
  MultTest m;
  MultTestTwo m2;
  int success;

  initial begin
    // Test 1: Multiplication with constant
    m = new;
    success = m.randomize();
    if (!success) begin
      $display("FAIL: MultTest randomize failed");
      $stop;
    end
    if (m.a <= 0 || m.a >= 100) begin
      $display("FAIL: a=%0d out of range", m.a);
      $stop;
    end
    if (m.b != m.a * 2) begin
      $display("FAIL: b=%0d, expected %0d (a*2)", m.b, m.a * 2);
      $stop;
    end
    if (m.c != m.a * 3) begin
      $display("FAIL: c=%0d, expected %0d (a*3)", m.c, m.a * 3);
      $stop;
    end
    $display("Test 1 PASS: a=%0d, b=%0d (a*2), c=%0d (a*3)", m.a, m.b, m.c);

    // Test 2: Multiplication with two variables
    m2 = new;
    success = m2.randomize() with { x == 5; y == 7; };
    if (!success) begin
      $display("FAIL: MultTestTwo randomize failed");
      $stop;
    end
    if (m2.z != 35) begin
      $display("FAIL: z=%0d, expected 35 (5*7)", m2.z);
      $stop;
    end
    $display("Test 2 PASS: x=%0d, y=%0d, z=%0d (x*y)", m2.x, m2.y, m2.z);

    // Test 3: std::randomize with multiplication
    begin
      int p, q;
      success = std::randomize(p, q) with { p > 0; p < 50; q == p * 2; };
      if (!success) begin
        $display("FAIL: std::randomize failed");
        $stop;
      end
      if (q != p * 2) begin
        $display("FAIL: q=%0d, expected %0d (p*2)", q, p * 2);
        $stop;
      end
      $display("Test 3 PASS: p=%0d, q=%0d (p*2)", p, q);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
