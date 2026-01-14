// DESCRIPTION: Verilator: Test inline constraints with inherited req member
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off WIDTHEXPAND */
/* verilator lint_off WIDTHTRUNC */

// Mimics the UVM pattern where req is inherited from parent class

class base_tx;
   rand bit [2:0] tx_type;
   rand bit [7:0] data;
endclass

// Parent sequence class that owns req (like uvm_sequence)
class base_seq;
   base_tx req;

   function new();
      req = new;
   endfunction

   // To be overridden by child classes
   virtual function int do_randomize();
      return req.randomize();
   endfunction
endclass

// Child sequence class (like axi4_master_write_seq)
class derived_seq extends base_seq;

   function int do_randomize();
      // Use inline constraint with inherited req member
      // This is the pattern used in UVM: req.randomize() with { req.member == value; }
      if (!req.randomize() with { req.tx_type == 3'd5; req.data == 8'd200; }) begin
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

      // Test: inherited member inline constraint
      $display("\n=== Test: inherited member inline constraint ===");
      for (int i = 0; i < 5; i++) begin
         if (seq.do_randomize()) begin
            if (seq.req.tx_type == 5 && seq.req.data == 200) begin
               $display("[PASS] tx_type=%0d (expected 5), data=%0d (expected 200)", seq.req.tx_type, seq.req.data);
               pass++;
            end else begin
               $display("[FAIL] tx_type=%0d (expected 5), data=%0d (expected 200)", seq.req.tx_type, seq.req.data);
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
