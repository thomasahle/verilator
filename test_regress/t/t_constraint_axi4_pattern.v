// DESCRIPTION: Verilator: Test AXI4-style constraints (queue + foreach + $countones)
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off WIDTHEXPAND */
/* verilator lint_off WIDTHTRUNC */
/* verilator lint_off CONSTRAINTIGN */

class axi4_tx;
   rand bit [7:0] awlen;
   rand bit [2:0] awsize;

   rand bit [31:0] wdata [$:256];
   rand bit [3:0] wstrb [$:256];

   // Size constraints
   constraint wdata_c { wdata.size() == awlen + 1; }
   constraint wstrb_c { wstrb.size() == awlen + 1; }

   // Foreach constraints
   constraint wstrb_nonzero { foreach(wstrb[i]) wstrb[i] != 0; }
   constraint wstrb_countones { foreach(wstrb[i]) $countones(wstrb[i]) == (1 << awsize); }

   // Limit test size
   constraint awlen_c { awlen inside {[0:7]}; }
   constraint awsize_c { awsize inside {[0:2]}; }

   function bit verify();
      bit ok = 1;
      if (wstrb.size() != awlen + 1) begin
         $display("[FAIL] wstrb.size=%0d, expected %0d", wstrb.size(), awlen+1);
         ok = 0;
      end
      for (int i = 0; i < wstrb.size(); i++) begin
         if (wstrb[i] == 0) begin
            $display("[FAIL] wstrb[%0d]=0", i);
            ok = 0;
         end
         if ($countones(wstrb[i]) != (1 << awsize)) begin
            $display("[FAIL] wstrb[%0d]=%b (%0d ones), expected %0d",
                     i, wstrb[i], $countones(wstrb[i]), 1 << awsize);
            ok = 0;
         end
      end
      return ok;
   endfunction
endclass

module t;
   axi4_tx tx;
   int pass = 0, fail = 0;

   initial begin
      // Test 1: New object each iteration (the harder case)
      $display("\n=== Test: New object each iteration ===");
      for (int i = 0; i < 5; i++) begin
         tx = new;  // Create NEW object each time
         if (tx.randomize()) begin
            $display("Iteration %0d: awlen=%0d, awsize=%0d, wstrb.size=%0d",
                     i, tx.awlen, tx.awsize, tx.wstrb.size());
            if (tx.verify()) begin
               pass++;
               $display("[PASS]");
            end else begin
               fail++;
               for (int j = 0; j < tx.wstrb.size(); j++)
                  $display("  wstrb[%0d]=%b", j, tx.wstrb[j]);
            end
         end else begin
            $display("[FAIL] randomize() returned 0");
            fail++;
         end
      end

      // Test 2: Reusing same object (the easier case - should always work)
      tx = new;
      $display("\n=== Test: Reusing same object ===");
      for (int i = 0; i < 5; i++) begin
         if (tx.randomize()) begin
            $display("Iteration %0d: awlen=%0d, awsize=%0d, wstrb.size=%0d",
                     i, tx.awlen, tx.awsize, tx.wstrb.size());
            if (tx.verify()) begin
               pass++;
               $display("[PASS]");
            end else begin
               fail++;
               for (int j = 0; j < tx.wstrb.size(); j++)
                  $display("  wstrb[%0d]=%b", j, tx.wstrb[j]);
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
