// DESCRIPTION: Verilator: Test inline constraints with parametric class inheritance
//
// This test demonstrates a known limitation: inline constraints with obj.member
// syntax don't work correctly when the object is inherited from a parametric class.
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
   // Test with WORKAROUND: omit the req. prefix
   function int do_test_workaround();
      if (!req.randomize() with { data == 8'd42; mode == 4'd3; }) begin
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

      // Test workaround pattern (should work)
      $display("\n=== Test: Parametric inline constraint (workaround) ===");
      if (seq.do_test_workaround()) begin
         if (seq.req.data == 42 && seq.req.mode == 3) begin
            $display("[PASS] Workaround: data=%0d, mode=%0d", seq.req.data, seq.req.mode);
            pass++;
         end else begin
            $display("[FAIL] Workaround: data=%0d (exp 42), mode=%0d (exp 3)", seq.req.data, seq.req.mode);
            fail++;
         end
      end else begin
         $display("[FAIL] Workaround: randomize returned 0");
         fail++;
      end

      // Repeat to verify consistency
      for (int i = 0; i < 4; i++) begin
         if (seq.do_test_workaround()) begin
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
