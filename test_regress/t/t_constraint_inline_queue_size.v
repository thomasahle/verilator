// DESCRIPTION: Verilator: Test inline constraints with queue size constraints
// This tests that randomize() with {...} properly resizes queues based on constraints
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class axi4_tx;
  rand bit [31:0] awaddr;
  rand bit [7:0] awlen;
  rand bit [1:0] awburst;
  rand bit [7:0] wdata [$:256];

  // Simple constraints
  constraint awlen_c {awlen inside {[0:3]};}
  constraint awburst_c {awburst != 2'b11;}

  // Queue size constraint
  constraint wdata_c1 {wdata.size() == awlen + 1;}

  function new();
  endfunction
endclass

module t;
  initial begin
    axi4_tx tx = new();
    int success;
    int errors = 0;

    $display("Testing inline constraints with queue size constraints...");

    // Test 1: Regular randomize (should work)
    success = tx.randomize();
    if (!success) begin
      $display("[FAIL] Test 1: Regular randomize() failed");
      errors++;
    end else if (tx.wdata.size() != tx.awlen + 1) begin
      $display("[FAIL] Test 1: Regular randomize() - wdata.size()=%0d, expected %0d",
               tx.wdata.size(), tx.awlen + 1);
      errors++;
    end else begin
      $display("[PASS] Test 1: Regular randomize() - awlen=%0d, wdata.size()=%0d",
               tx.awlen, tx.wdata.size());
    end

    // Test 2: Inline constraint (this was the bug - queue size became 0)
    success = tx.randomize() with {
      awaddr < 32'h1000;
    };
    if (!success) begin
      $display("[FAIL] Test 2: Inline randomize() failed");
      errors++;
    end else if (tx.wdata.size() != tx.awlen + 1) begin
      $display("[FAIL] Test 2: Inline randomize() - wdata.size()=%0d, expected %0d",
               tx.wdata.size(), tx.awlen + 1);
      errors++;
    end else begin
      $display("[PASS] Test 2: Inline randomize() - awlen=%0d, wdata.size()=%0d, awaddr=0x%0h",
               tx.awlen, tx.wdata.size(), tx.awaddr);
    end

    // Test 3: Another inline constraint on different variable
    success = tx.randomize() with {
      awburst == 2'b01;
    };
    if (!success) begin
      $display("[FAIL] Test 3: Inline randomize() with awburst failed");
      errors++;
    end else if (tx.wdata.size() != tx.awlen + 1) begin
      $display("[FAIL] Test 3: Inline randomize() - wdata.size()=%0d, expected %0d",
               tx.wdata.size(), tx.awlen + 1);
      errors++;
    end else begin
      $display("[PASS] Test 3: Inline randomize() with awburst - awlen=%0d, wdata.size()=%0d",
               tx.awlen, tx.wdata.size());
    end

    // Test 4: Inline constraint that affects queue size
    success = tx.randomize() with {
      awlen == 2;
    };
    if (!success) begin
      $display("[FAIL] Test 4: Inline randomize() with awlen==2 failed");
      errors++;
    end else if (tx.wdata.size() != 3) begin
      $display("[FAIL] Test 4: wdata.size()=%0d, expected 3", tx.wdata.size());
      errors++;
    end else begin
      $display("[PASS] Test 4: awlen=2, wdata.size()=%0d (expected 3)", tx.wdata.size());
    end

    if (errors == 0) begin
      $display("*-* All Finished *-*");
    end else begin
      $display("[FAIL] %0d errors occurred", errors);
    end
    $finish;
  end
endmodule
