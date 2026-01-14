// DESCRIPTION: Verilator: Test inline constraints with obj.randomize() with {obj.member}
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off WIDTHEXPAND */
/* verilator lint_off WIDTHTRUNC */

class simple_tx;
   rand bit [2:0] value;
   rand bit [7:0] data;
endclass

class sequence_item;
   simple_tx req;

   function new();
      req = new;
   endfunction

   // Test using obj.member style inside with clause
   function int do_randomize();
      // This is the pattern used in UVM sequences: req.randomize() with { req.value == 5; }
      if (!req.randomize() with { req.value == 3'd5; req.data == 8'd100; }) begin
         return 0;
      end
      return 1;
   endfunction
endclass

module t;
   sequence_item seq;
   int pass = 0, fail = 0;

   initial begin
      seq = new;

      // Test: obj.member style inline constraint
      $display("\n=== Test: obj.member style inline constraint ===");
      if (seq.do_randomize()) begin
         if (seq.req.value == 5 && seq.req.data == 100) begin
            $display("[PASS] value=%0d (expected 5), data=%0d (expected 100)", seq.req.value, seq.req.data);
            pass++;
         end else begin
            $display("[FAIL] value=%0d (expected 5), data=%0d (expected 100)", seq.req.value, seq.req.data);
            fail++;
         end
      end else begin
         $display("[FAIL] randomize() returned 0");
         fail++;
      end

      // Repeat a few times
      for (int i = 0; i < 4; i++) begin
         if (seq.do_randomize()) begin
            if (seq.req.value == 5 && seq.req.data == 100) begin
               $display("[PASS] value=%0d, data=%0d", seq.req.value, seq.req.data);
               pass++;
            end else begin
               $display("[FAIL] value=%0d, data=%0d", seq.req.value, seq.req.data);
               fail++;
            end
         end else begin
            $display("[FAIL] randomize() returned 0");
            fail++;
         end
      end

      $display("\n=== Final: %0d pass, %0d fail ===", pass, fail);
      if (fail == 0) $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
