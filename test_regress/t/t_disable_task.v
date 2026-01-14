// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test disable task by name with fork join_none (background threads)

int x = 0;

task increment_x;
  repeat (100) begin
    x++;
    #1;
  end
endtask

class driver;
  int m_time = 0;

  task get_and_send();
    forever begin
      #10;
      m_time += 10;
    end
  endtask

  task post_shutdown_phase();
    disable get_and_send;
  endtask
endclass

module t;

  driver c;

  initial begin
    // Test 1: Simple task disable with join_none
    fork
      increment_x();
    join_none

    #5;
    if (x != 5) $stop;
    disable increment_x;
    #10;
    // Task should have stopped, x should still be 5
    if (x != 5) $stop;

    // Test 2: Class method task disable (UVM pattern)
    c = new;
    fork
      c.get_and_send;
    join_none
    if (c.m_time != 0) $stop;

    #11;
    if (c.m_time != 10) $stop;

    #20;
    if (c.m_time != 30) $stop;
    c.post_shutdown_phase;

    #20;
    // Task should have stopped, m_time should still be 30
    if (c.m_time != 30) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
