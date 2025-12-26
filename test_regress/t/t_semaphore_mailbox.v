// DESCRIPTION: Verilator: Test semaphores and mailboxes
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test semaphores and mailboxes used in UVM synchronization

module t;
  // Test semaphore
  task automatic test_semaphore();
    semaphore sem;
    int acquired = 0;

    $display("[%0t] test_semaphore: Starting", $time);

    sem = new(2);  // 2 keys available

    // Get 2 keys
    sem.get(1);
    acquired++;
    $display("[%0t] Got 1 key, total acquired=%0d", $time, acquired);

    sem.get(1);
    acquired++;
    $display("[%0t] Got 1 key, total acquired=%0d", $time, acquired);

    // Try to get more (should block if we wait, but use try_get)
    if (sem.try_get(1)) begin
      $display("ERROR: try_get should have failed");
      $stop;
    end
    $display("[%0t] try_get correctly returned 0 (no keys available)", $time);

    // Put back keys
    sem.put(2);
    $display("[%0t] Put 2 keys back", $time);

    // Now we can get again
    if (!sem.try_get(1)) begin
      $display("ERROR: try_get should have succeeded");
      $stop;
    end
    $display("[%0t] try_get succeeded after put", $time);

    $display("[%0t] test_semaphore: PASSED", $time);
  endtask

  // Test mailbox
  task automatic test_mailbox();
    mailbox #(int) mb;
    int data;
    int result;

    $display("[%0t] test_mailbox: Starting", $time);

    mb = new(4);  // Bounded mailbox with 4 slots

    // Put some items
    mb.put(10);
    $display("[%0t] Put 10, num=%0d", $time, mb.num());
    mb.put(20);
    $display("[%0t] Put 20, num=%0d", $time, mb.num());
    mb.put(30);
    $display("[%0t] Put 30, num=%0d", $time, mb.num());

    // Get items
    mb.get(data);
    if (data != 10) begin
      $display("ERROR: Expected 10, got %0d", data);
      $stop;
    end
    $display("[%0t] Got %0d (expected 10)", $time, data);

    // Peek at next item (non-destructive)
    mb.peek(data);
    if (data != 20) begin
      $display("ERROR: Peek expected 20, got %0d", data);
      $stop;
    end
    $display("[%0t] Peek %0d (expected 20), num=%0d", $time, data, mb.num());

    // Try get
    result = mb.try_get(data);
    if (result != 1 || data != 20) begin
      $display("ERROR: try_get failed or wrong data");
      $stop;
    end
    $display("[%0t] try_get returned %0d (expected 20)", $time, data);

    $display("[%0t] test_mailbox: PASSED", $time);
  endtask

  // Test blocking mailbox with fork
  task automatic test_mailbox_blocking();
    mailbox #(string) mb;
    string msg;
    bit producer_done = 0;
    bit consumer_done = 0;

    $display("[%0t] test_mailbox_blocking: Starting", $time);

    mb = new();  // Unbounded mailbox

    fork
      // Producer
      begin
        #10;
        mb.put("Hello");
        $display("[%0t] Producer: sent 'Hello'", $time);
        #10;
        mb.put("World");
        $display("[%0t] Producer: sent 'World'", $time);
        producer_done = 1;
      end

      // Consumer
      begin
        mb.get(msg);
        $display("[%0t] Consumer: received '%s'", $time, msg);
        if (msg != "Hello") begin
          $display("ERROR: Expected 'Hello'");
          $stop;
        end
        mb.get(msg);
        $display("[%0t] Consumer: received '%s'", $time, msg);
        if (msg != "World") begin
          $display("ERROR: Expected 'World'");
          $stop;
        end
        consumer_done = 1;
      end
    join

    if (!producer_done || !consumer_done) begin
      $display("ERROR: Tasks did not complete");
      $stop;
    end

    $display("[%0t] test_mailbox_blocking: PASSED", $time);
  endtask

  initial begin
    $display("=== Semaphore and Mailbox Tests ===");

    test_semaphore();
    #10;

    test_mailbox();
    #10;

    test_mailbox_blocking();

    $display("\n=== All Tests PASSED ===");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
