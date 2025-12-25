// DESCRIPTION: Verilator: Test inline constraints with parametric class inheritance
//              using obj.member prefix syntax
//
// This test verifies that inline constraints with obj.member syntax work correctly
// when the object is inherited from a parametric class. This pattern is common
// in UVM sequences where req inherits from uvm_sequence#(REQ).
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off WIDTHEXPAND */
/* verilator lint_off WIDTHTRUNC */

class tx_item;
   rand bit [7:0] data;
   rand bit [3:0] mode;

   function new();
   endfunction
endclass

// Parametric base class - similar to uvm_sequence#(REQ)
class base_seq #(type REQ = tx_item);
   REQ req;

   function new();
      req = new;
   endfunction
endclass

// Derived class - similar to user's UVM sequence
class derived_seq extends base_seq #(tx_item);
   // Test with obj.member prefix - was broken before fix
   function int do_test_prefix();
      if (!req.randomize() with { req.data == 8'd42; req.mode == 4'd3; }) begin
         return 0;
      end
      return 1;
   endfunction

   // Test without prefix - always worked
   function int do_test_no_prefix();
      if (!req.randomize() with { data == 8'd100; mode == 4'd7; }) begin
         return 0;
      end
      return 1;
   endfunction
endclass

module t;
   derived_seq seq;
   int pass = 0, fail = 0;

   initial begin
      seq = new;

      // Test with obj.member prefix
      $display("\n=== Test: Parametric inline constraint (with prefix) ===");
      if (seq.do_test_prefix()) begin
         if (seq.req.data == 42 && seq.req.mode == 3) begin
            $display("[PASS] With prefix: data=%0d, mode=%0d", seq.req.data, seq.req.mode);
            pass++;
         end else begin
            $display("[FAIL] With prefix: data=%0d (exp 42), mode=%0d (exp 3)", seq.req.data, seq.req.mode);
            fail++;
         end
      end else begin
         $display("[FAIL] With prefix: randomize returned 0");
         fail++;
      end

      // Test without prefix
      $display("\n=== Test: Parametric inline constraint (no prefix) ===");
      if (seq.do_test_no_prefix()) begin
         if (seq.req.data == 100 && seq.req.mode == 7) begin
            $display("[PASS] No prefix: data=%0d, mode=%0d", seq.req.data, seq.req.mode);
            pass++;
         end else begin
            $display("[FAIL] No prefix: data=%0d (exp 100), mode=%0d (exp 7)", seq.req.data, seq.req.mode);
            fail++;
         end
      end else begin
         $display("[FAIL] No prefix: randomize returned 0");
         fail++;
      end

      // Repeat to verify consistency
      for (int i = 0; i < 3; i++) begin
         if (seq.do_test_prefix()) begin
            if (seq.req.data == 42 && seq.req.mode == 3) begin
               $display("[PASS] data=%0d, mode=%0d", seq.req.data, seq.req.mode);
               pass++;
            end else begin
               $display("[FAIL] data=%0d (exp 42), mode=%0d (exp 3)", seq.req.data, seq.req.mode);
               fail++;
            end
         end else begin
            $display("[FAIL] randomize returned 0");
            fail++;
         end
      end

      $display("\n=== Final: %0d pass, %0d fail ===", pass, fail);
      if (fail == 0) $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
