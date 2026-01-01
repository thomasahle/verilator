// DESCRIPTION: Verilator: Test for negedge event scheduling
// Tests that @(negedge signal) in a task called from run_phase catches
// edges that occur during simulation startup.
//
// This pattern is used in UVM BFMs that wait for reset:
//   task wait_for_reset();
//     @(negedge reset_n);  // Wait for reset assertion
//     @(posedge reset_n);  // Wait for reset de-assertion
//   endtask
//
// In commercial simulators, this works because the task starts
// before or at the same time as the reset edge. In Verilator,
// if the task starts AFTER the negedge, it blocks forever.

module t;
  bit clk;
  bit reset_n;

  // Track if we saw the edges
  bit saw_negedge = 0;
  bit saw_posedge = 0;
  bit task_started = 0;
  bit task_completed = 0;

  // Clock generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  // Reset generation - same pattern as APB AVIP
  // reset_n: 1 -> 0 (at #15) -> 1 (after posedge clk)
  initial begin
    reset_n = 1'b1;
    #15 reset_n = 1'b0;  // negedge at time 15
    @(posedge clk);
    reset_n = 1'b1;      // posedge sometime after
  end

  // Task that waits for reset - called from a parallel process
  task automatic wait_for_reset();
    task_started = 1;
    $display("[%0t] wait_for_reset: Starting, reset_n=%b", $time, reset_n);

    @(negedge reset_n);
    saw_negedge = 1;
    $display("[%0t] wait_for_reset: Saw negedge, reset_n=%b", $time, reset_n);

    @(posedge reset_n);
    saw_posedge = 1;
    $display("[%0t] wait_for_reset: Saw posedge, reset_n=%b", $time, reset_n);

    task_completed = 1;
    $display("[%0t] wait_for_reset: Complete", $time);
  endtask

  // Simulate UVM run_phase - starts at time 0
  initial begin
    $display("[%0t] run_phase: Starting", $time);

    // Call the wait_for_reset task (like UVM driver proxy does)
    wait_for_reset();

    $display("[%0t] run_phase: wait_for_reset returned", $time);
  end

  // Timeout and check
  initial begin
    #100;

    $display("");
    $display("=== Results ===");
    $display("task_started: %b", task_started);
    $display("saw_negedge: %b", saw_negedge);
    $display("saw_posedge: %b", saw_posedge);
    $display("task_completed: %b", task_completed);

    if (!task_completed) begin
      $display("%%Error: Task did not complete - missed negedge event");
      $stop;
    end else begin
      $display("*-* All Finished *-*");
      $finish;
    end
  end

endmodule
