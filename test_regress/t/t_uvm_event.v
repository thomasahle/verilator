// DESCRIPTION: Verilator: Test UVM event and barrier synchronization
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test uvm_event and uvm_barrier synchronization primitives

`include "uvm_macros.svh"

module t;
  import uvm_pkg::*;

  // Test basic uvm_event trigger and wait
  task automatic test_event_basic();
    uvm_event #(uvm_object) ev;
    bit producer_done = 0;
    bit consumer_done = 0;

    $display("[%0t] test_event_basic: Starting", $time);

    ev = new("test_event");

    // Verify initial state
    if (ev.is_on()) begin
      $display("ERROR: Event should be off initially");
      $stop;
    end
    $display("[%0t] Event is_off=%0d (expected 1)", $time, ev.is_off());

    fork
      // Producer - triggers event after delay
      begin
        #20;
        $display("[%0t] Producer: Triggering event", $time);
        ev.trigger();
        producer_done = 1;
      end

      // Consumer - waits for event
      begin
        $display("[%0t] Consumer: Waiting for event", $time);
        ev.wait_trigger();
        $display("[%0t] Consumer: Event triggered!", $time);
        consumer_done = 1;
      end
    join

    if (!producer_done || !consumer_done) begin
      $display("ERROR: Tasks did not complete");
      $stop;
    end

    // Verify event state after trigger
    if (!ev.is_on()) begin
      $display("ERROR: Event should be on after trigger");
      $stop;
    end
    $display("[%0t] Event is_on=%0d (expected 1)", $time, ev.is_on());

    $display("[%0t] test_event_basic: PASSED", $time);
  endtask

  // Test uvm_event with data
  task automatic test_event_data();
    uvm_event #(int) ev;
    int received_data;

    $display("[%0t] test_event_data: Starting", $time);

    ev = new("data_event");

    fork
      // Producer
      begin
        #15;
        $display("[%0t] Producer: Triggering with data=42", $time);
        ev.trigger(42);
      end

      // Consumer
      begin
        $display("[%0t] Consumer: Waiting for data", $time);
        ev.wait_trigger_data(received_data);
        $display("[%0t] Consumer: Received data=%0d", $time, received_data);
        if (received_data != 42) begin
          $display("ERROR: Expected data=42, got %0d", received_data);
          $stop;
        end
      end
    join

    $display("[%0t] test_event_data: PASSED", $time);
  endtask

  // Test uvm_event reset
  task automatic test_event_reset();
    uvm_event #(uvm_object) ev;

    $display("[%0t] test_event_reset: Starting", $time);

    ev = new("reset_event");

    // Trigger the event
    ev.trigger();
    if (!ev.is_on()) begin
      $display("ERROR: Event should be on after trigger");
      $stop;
    end
    $display("[%0t] After trigger: is_on=%0d", $time, ev.is_on());

    // Reset the event
    ev.reset();
    if (!ev.is_off()) begin
      $display("ERROR: Event should be off after reset");
      $stop;
    end
    $display("[%0t] After reset: is_off=%0d", $time, ev.is_off());

    // Check trigger time was recorded
    ev.trigger();
    if (ev.get_trigger_time() != $time) begin
      $display("ERROR: Trigger time mismatch");
      $stop;
    end
    $display("[%0t] Trigger time=%0t (expected %0t)", $time, ev.get_trigger_time(), $time);

    $display("[%0t] test_event_reset: PASSED", $time);
  endtask

  // Test uvm_event wait_on (already triggered)
  task automatic test_event_wait_on();
    uvm_event #(uvm_object) ev;
    bit done = 0;

    $display("[%0t] test_event_wait_on: Starting", $time);

    ev = new("wait_on_event");

    // Trigger first
    ev.trigger();
    $display("[%0t] Event triggered first", $time);

    // wait_on should return immediately since event is already on
    fork
      begin
        ev.wait_on();
        $display("[%0t] wait_on returned (should be immediate)", $time);
        done = 1;
      end
      begin
        #10;
        if (!done) begin
          $display("ERROR: wait_on should have returned immediately");
          $stop;
        end
      end
    join_any
    disable fork;

    if (!done) begin
      $display("ERROR: wait_on did not complete");
      $stop;
    end

    $display("[%0t] test_event_wait_on: PASSED", $time);
  endtask

  // Test uvm_barrier
  task automatic test_barrier_basic();
    uvm_barrier barrier;
    int completed = 0;

    $display("[%0t] test_barrier_basic: Starting", $time);

    barrier = new("test_barrier", 3);  // Wait for 3 processes
    $display("[%0t] Barrier threshold=%0d", $time, barrier.get_threshold());

    fork
      // Process 1
      begin
        #10;
        $display("[%0t] Process 1: Waiting at barrier", $time);
        barrier.wait_for();
        $display("[%0t] Process 1: Released!", $time);
        completed++;
      end

      // Process 2
      begin
        #20;
        $display("[%0t] Process 2: Waiting at barrier", $time);
        barrier.wait_for();
        $display("[%0t] Process 2: Released!", $time);
        completed++;
      end

      // Process 3
      begin
        #30;
        $display("[%0t] Process 3: Waiting at barrier", $time);
        barrier.wait_for();
        $display("[%0t] Process 3: Released!", $time);
        completed++;
      end
    join

    if (completed != 3) begin
      $display("ERROR: Not all processes completed, count=%0d", completed);
      $stop;
    end

    $display("[%0t] test_barrier_basic: PASSED", $time);
  endtask

  // Test uvm_barrier reset
  task automatic test_barrier_reset();
    uvm_barrier barrier;
    int completed = 0;
    bit process1_started = 0;
    bit process2_started = 0;

    $display("[%0t] test_barrier_reset: Starting", $time);

    barrier = new("reset_barrier", 3);

    fork
      // Process 1 - will be reset before all arrive
      begin
        #5;
        process1_started = 1;
        $display("[%0t] Process 1: Waiting at barrier", $time);
        barrier.wait_for();
        $display("[%0t] Process 1: Released (via reset)", $time);
        completed++;
      end

      // Process 2
      begin
        #10;
        process2_started = 1;
        $display("[%0t] Process 2: Waiting at barrier", $time);
        barrier.wait_for();
        $display("[%0t] Process 2: Released (via reset)", $time);
        completed++;
      end

      // Reset the barrier after some processes are waiting
      begin
        #15;
        $display("[%0t] Resetting barrier with %0d waiters", $time, barrier.get_num_waiters());
        barrier.reset(1);  // Wakeup waiters
      end
    join

    // Both waiting processes should have been released by reset
    if (completed != 2) begin
      $display("ERROR: Expected 2 processes released by reset, got %0d", completed);
      $stop;
    end

    $display("[%0t] test_barrier_reset: PASSED", $time);
  endtask

  initial begin
    $display("=== UVM Event and Barrier Tests ===");

    test_event_basic();
    #10;

    test_event_data();
    #10;

    test_event_reset();
    #10;

    test_event_wait_on();
    #10;

    test_barrier_basic();
    #10;

    test_barrier_reset();

    $display("\n=== All Tests PASSED ===");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
