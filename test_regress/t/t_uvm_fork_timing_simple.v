// DESCRIPTION: Verilator: Simple test for fork/join_none with timing in task
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
  class MyClass;
    task run_a();
      $display("[%0t] run_a starting", $time);
      #10;
      $display("[%0t] run_a after delay", $time);
    endtask

    task run_b();
      $display("[%0t] run_b starting", $time);
      #20;
      $display("[%0t] run_b after delay", $time);
    endtask

    task do_fork();
      $display("[%0t] do_fork: before fork", $time);
      fork
        run_a();
      join_none
      $display("[%0t] do_fork: after join_none, before #1", $time);
      fork
        run_b();
      join_none
      $display("[%0t] do_fork: after second join_none, before #5", $time);
      #5;
      $display("[%0t] do_fork: after #5", $time);
      #50;
      $display("[%0t] do_fork: after #50", $time);
    endtask
  endclass

  initial begin
    MyClass c = new();
    $display("[%0t] Calling do_fork", $time);
    c.do_fork();
    $display("[%0t] do_fork returned", $time);
    $write("*-* All Finished *-*\n");
    $finish;
  end

  initial #100 $stop; // timeout
endmodule
