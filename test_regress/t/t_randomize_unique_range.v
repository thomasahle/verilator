// DESCRIPTION: Verilator: Test unique constraint with range constraints
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0
//
// Tests that unique constraint works correctly when combined with
// other constraints (like range constraints). Issue: unique constraint
// expansion must preserve user1() flags for SMT constraint generation.

class unique_range_test;
   rand bit [7:0] a, b;
   constraint c_range { a < 10; b < 10; }
   constraint c_unique { unique { a, b }; }

   function new();
      a = 0;
      b = 0;
   endfunction

   function void check();
      if (a == b) begin
         $display("ERROR: a == b (%0d)", a);
         $stop;
      end
      if (a >= 10 || b >= 10) begin
         $display("ERROR: out of range a=%0d, b=%0d", a, b);
         $stop;
      end
   endfunction
endclass

// Test with signed int type
class unique_int_test;
   rand int x, y;
   constraint c_range { x >= 0; x < 100; y >= 0; y < 100; }
   constraint c_unique { unique { x, y }; }

   function new();
      x = 0;
      y = 0;
   endfunction

   function void check();
      if (x == y) begin
         $display("ERROR: x == y (%0d)", x);
         $stop;
      end
      if (x < 0 || x >= 100 || y < 0 || y >= 100) begin
         $display("ERROR: out of range x=%0d, y=%0d", x, y);
         $stop;
      end
   endfunction
endclass

// Test with three values
class unique_triple_range;
   rand bit [7:0] a, b, c;
   constraint c_range { a < 20; b < 20; c < 20; }
   constraint c_unique { unique { a, b, c }; }

   function new();
      a = 0;
      b = 0;
      c = 0;
   endfunction

   function void check();
      if (a == b || a == c || b == c) begin
         $display("ERROR: not unique a=%0d, b=%0d, c=%0d", a, b, c);
         $stop;
      end
      if (a >= 20 || b >= 20 || c >= 20) begin
         $display("ERROR: out of range a=%0d, b=%0d, c=%0d", a, b, c);
         $stop;
      end
   endfunction
endclass

module t;
   unique_range_test obj1;
   unique_int_test obj2;
   unique_triple_range obj3;

   initial begin
      // Test 1: unique with bit type and range
      obj1 = new();
      repeat(10) begin
         if (obj1.randomize() != 1) begin
            $display("ERROR: randomize() failed for obj1");
            $stop;
         end
         obj1.check();
         $display("Test1: a=%0d, b=%0d", obj1.a, obj1.b);
      end

      // Test 2: unique with int type and range
      obj2 = new();
      repeat(10) begin
         if (obj2.randomize() != 1) begin
            $display("ERROR: randomize() failed for obj2");
            $stop;
         end
         obj2.check();
         $display("Test2: x=%0d, y=%0d", obj2.x, obj2.y);
      end

      // Test 3: unique with three variables and range
      obj3 = new();
      repeat(10) begin
         if (obj3.randomize() != 1) begin
            $display("ERROR: randomize() failed for obj3");
            $stop;
         end
         obj3.check();
         $display("Test3: a=%0d, b=%0d, c=%0d", obj3.a, obj3.b, obj3.c);
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
