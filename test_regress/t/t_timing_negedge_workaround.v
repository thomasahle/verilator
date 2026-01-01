// DESCRIPTION: Verilator: Test workaround for negedge event scheduling
// Uses wait() instead of @(negedge) to work around the bug

module t;
  bit clk;
  bit reset_n;

  bit saw_low = 0;
  bit saw_high = 0;
  bit task_completed = 0;

  // Clock generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  // Reset generation - same pattern as APB AVIP
  initial begin
    reset_n = 1'b1;
    #15 reset_n = 1'b0;  // negedge at time 15
    @(posedge clk);
    reset_n = 1'b1;      // posedge sometime after
  end

  // Alternative wait_for_reset using wait() instead of @(negedge)
  task automatic wait_for_reset();
    $display("[%0t] wait_for_reset: Starting, reset_n=%b", $time, reset_n);

    // Workaround: Use wait() instead of @(negedge)
    wait(reset_n == 0);  // Wait for reset to be asserted
    saw_low = 1;
    $display("[%0t] wait_for_reset: reset_n went low", $time);

    wait(reset_n == 1);  // Wait for reset to be deasserted
    saw_high = 1;
    $display("[%0t] wait_for_reset: reset_n went high", $time);

    task_completed = 1;
    $display("[%0t] wait_for_reset: Complete", $time);
  endtask

  initial begin
    $display("[%0t] run_phase: Starting", $time);
    wait_for_reset();
    $display("[%0t] run_phase: wait_for_reset returned", $time);
  end

  initial begin
    #100;
    if (!task_completed) begin
      $display("%%Error: Task did not complete");
      $stop;
    end else begin
      $display("*-* All Finished *-*");
      $finish;
    end
  end
endmodule
