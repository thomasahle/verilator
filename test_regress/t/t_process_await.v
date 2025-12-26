// DESCRIPTION: Verilator: Test process handles and await
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test process::self() and await() used in UVM virtual sequences

module t;
  int task1_done = 0;
  int task2_done = 0;
  int task3_done = 0;

  // Test basic process handle and await
  task automatic test_basic_await();
    process p;
    $display("[%0t] test_basic_await: Starting", $time);

    fork
      begin
        p = process::self();
        $display("[%0t] Background task started, process=%p", $time, p);
        #50;
        $display("[%0t] Background task completing", $time);
        task1_done = 1;
      end
    join_none

    #10;
    $display("[%0t] Waiting for background task, status=%s", $time, p.status().name());

    p.await();
    $display("[%0t] Background task completed, status=%s", $time, p.status().name());

    if (task1_done != 1) begin
      $display("ERROR: task1 should be done");
      $stop;
    end
    $display("[%0t] test_basic_await: PASSED", $time);
  endtask

  // Test multiple processes with await
  task automatic test_multiple_processes();
    process p1, p2;
    $display("[%0t] test_multiple_processes: Starting", $time);

    fork
      begin
        p1 = process::self();
        $display("[%0t] Task1 started", $time);
        #30;
        task2_done = 1;
        $display("[%0t] Task1 done", $time);
      end
      begin
        p2 = process::self();
        $display("[%0t] Task2 started", $time);
        #60;
        task3_done = 1;
        $display("[%0t] Task2 done", $time);
      end
    join_none

    #10;
    $display("[%0t] Waiting for p1 (status=%s)", $time, p1.status().name());
    p1.await();
    $display("[%0t] p1 completed", $time);

    if (task2_done != 1) begin
      $display("ERROR: task2 should be done");
      $stop;
    end

    $display("[%0t] Waiting for p2 (status=%s)", $time, p2.status().name());
    p2.await();
    $display("[%0t] p2 completed", $time);

    if (task3_done != 1) begin
      $display("ERROR: task3 should be done");
      $stop;
    end

    $display("[%0t] test_multiple_processes: PASSED", $time);
  endtask

  // Test process status
  task automatic test_process_status();
    process p;
    $display("[%0t] test_process_status: Starting", $time);

    fork
      begin
        p = process::self();
        #20;
      end
    join_none

    #5;
    if (p.status() != process::WAITING) begin
      $display("ERROR: Expected WAITING, got %s", p.status().name());
      $stop;
    end
    $display("[%0t] Status is WAITING as expected", $time);

    p.await();

    if (p.status() != process::FINISHED) begin
      $display("ERROR: Expected FINISHED, got %s", p.status().name());
      $stop;
    end
    $display("[%0t] Status is FINISHED as expected", $time);
    $display("[%0t] test_process_status: PASSED", $time);
  endtask

  initial begin
    $display("=== Process Handle Tests ===");

    test_basic_await();
    #10;

    test_multiple_processes();
    #10;

    test_process_status();

    $display("\n=== All Tests PASSED ===");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
