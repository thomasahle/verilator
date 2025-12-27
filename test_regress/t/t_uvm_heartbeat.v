// DESCRIPTION: Verilator: Test UVM heartbeat functionality
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test uvm_heartbeat

`include "uvm_macros.svh"

module t;
  import uvm_pkg::*;

  // Test heartbeat creation and basic methods
  task automatic test_heartbeat_basic();
    uvm_heartbeat hb;
    uvm_component comp_list[$];

    $display("[%0t] test_heartbeat_basic: Starting", $time);

    hb = new("test_hb");
    if (hb == null) begin
      $display("ERROR: Failed to create heartbeat");
      $stop;
    end

    // Test set_mode
    hb.set_mode(UVM_ALL_ACTIVE);

    // Test set_heartbeat
    hb.set_heartbeat(100, comp_list);

    // Test is_started
    if (hb.is_started()) begin
      $display("ERROR: Heartbeat should not be started yet");
      $stop;
    end

    $display("[%0t] test_heartbeat_basic: PASSED", $time);
  endtask

  // Test heartbeat with activity
  task automatic test_heartbeat_activity();
    uvm_heartbeat hb;
    uvm_component comp_list[$];

    $display("[%0t] test_heartbeat_activity: Starting", $time);

    hb = new("activity_hb");
    hb.set_mode(UVM_ONE_ACTIVE);
    hb.set_heartbeat(50, comp_list);

    // Start heartbeat in background
    fork
      hb.start();
    join_none

    // Generate some heartbeats
    repeat (5) begin
      #10;
      hb.raise_objection();
    end

    #10;

    // Stop heartbeat
    hb.stop();

    if (hb.is_started()) begin
      $display("ERROR: Heartbeat should be stopped");
      $stop;
    end

    $display("[%0t] test_heartbeat_activity: PASSED", $time);
  endtask

  // Test heartbeat modes enum
  task automatic test_heartbeat_modes();
    uvm_heartbeat_modes mode;

    $display("[%0t] test_heartbeat_modes: Starting", $time);

    mode = UVM_NO_HB_MODE;
    if (mode != 0) begin
      $display("ERROR: UVM_NO_HB_MODE should be 0");
      $stop;
    end

    mode = UVM_ALL_ACTIVE;
    if (mode != 1) begin
      $display("ERROR: UVM_ALL_ACTIVE should be 1");
      $stop;
    end

    mode = UVM_ONE_ACTIVE;
    if (mode != 2) begin
      $display("ERROR: UVM_ONE_ACTIVE should be 2");
      $stop;
    end

    mode = UVM_ANY_ACTIVE;
    if (mode != 3) begin
      $display("ERROR: UVM_ANY_ACTIVE should be 3");
      $stop;
    end

    $display("[%0t] test_heartbeat_modes: PASSED", $time);
  endtask

  // Test add/remove component
  task automatic test_heartbeat_add_remove();
    uvm_heartbeat hb;
    uvm_component comp;

    $display("[%0t] test_heartbeat_add_remove: Starting", $time);

    hb = new("add_remove_hb");

    // Create a dummy component
    comp = new("dummy_comp", null);

    // Add component
    hb.add(comp);

    // Remove component
    hb.remove(comp);

    $display("[%0t] test_heartbeat_add_remove: PASSED", $time);
  endtask

  initial begin
    $display("=== UVM Heartbeat Tests ===");

    test_heartbeat_basic();
    #10;

    test_heartbeat_modes();
    #10;

    test_heartbeat_add_remove();
    #10;

    test_heartbeat_activity();

    $display("\n=== All Tests PASSED ===");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
