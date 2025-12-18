// DESCRIPTION: Verilator: Test UVM objection mechanism
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`include "uvm_macros.svh"
import uvm_pkg::*;

//----------------------------------------------------------------------
// Test component that raises and drops objections
//----------------------------------------------------------------------
class objection_test_component extends uvm_component;
  `uvm_component_utils(objection_test_component)

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual task run_phase(uvm_phase phase);
    `uvm_info("COMP", "Starting run_phase, raising objection", UVM_LOW)
    phase.raise_objection(this, "Starting work");

    // Simulate doing some work
    `uvm_info("COMP", $sformatf("Objection count after raise: %0d", phase.get_objection_count()), UVM_LOW)

    // Drop the objection when done
    `uvm_info("COMP", "Work complete, dropping objection", UVM_LOW)
    phase.drop_objection(this, "Work complete");
    `uvm_info("COMP", $sformatf("Objection count after drop: %0d", phase.get_objection_count()), UVM_LOW)
  endtask
endclass

//----------------------------------------------------------------------
// Test
//----------------------------------------------------------------------
class objection_test extends uvm_test;
  `uvm_component_utils(objection_test)

  objection_test_component comp1;
  objection_test_component comp2;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    comp1 = objection_test_component::type_id::create("comp1", this);
    comp2 = objection_test_component::type_id::create("comp2", this);
  endfunction

  virtual task run_phase(uvm_phase phase);
    int pass_count = 0;
    int fail_count = 0;

    `uvm_info("TEST", "Starting objection mechanism test", UVM_LOW)

    // Test 1: Initial state - no objections
    `uvm_info("TEST", "Test 1: Checking initial state", UVM_LOW)
    if (phase.phase_done()) begin
      `uvm_info("TEST", "PASS: Phase initially has no objections", UVM_LOW)
      pass_count++;
    end else begin
      `uvm_error("TEST", "FAIL: Phase should have no initial objections")
      fail_count++;
    end

    // Test 2: Raise objection and check count
    `uvm_info("TEST", "Test 2: Raise objection", UVM_LOW)
    phase.raise_objection(this, "test objection");
    if (phase.get_objection_count() == 1) begin
      `uvm_info("TEST", "PASS: Objection count is 1 after raise", UVM_LOW)
      pass_count++;
    end else begin
      `uvm_error("TEST", $sformatf("FAIL: Expected count 1, got %0d", phase.get_objection_count()))
      fail_count++;
    end

    // Test 3: Raise another objection
    `uvm_info("TEST", "Test 3: Raise second objection", UVM_LOW)
    phase.raise_objection(comp1, "comp1 objection");
    if (phase.get_objection_count() == 2) begin
      `uvm_info("TEST", "PASS: Objection count is 2 after second raise", UVM_LOW)
      pass_count++;
    end else begin
      `uvm_error("TEST", $sformatf("FAIL: Expected count 2, got %0d", phase.get_objection_count()))
      fail_count++;
    end

    // Test 4: Check phase_done (should be false)
    `uvm_info("TEST", "Test 4: Check phase_done with active objections", UVM_LOW)
    if (!phase.phase_done()) begin
      `uvm_info("TEST", "PASS: phase_done correctly returns 0 with active objections", UVM_LOW)
      pass_count++;
    end else begin
      `uvm_error("TEST", "FAIL: phase_done should return 0 with active objections")
      fail_count++;
    end

    // Test 5: Drop one objection
    `uvm_info("TEST", "Test 5: Drop one objection", UVM_LOW)
    phase.drop_objection(this, "done");
    if (phase.get_objection_count() == 1) begin
      `uvm_info("TEST", "PASS: Objection count is 1 after drop", UVM_LOW)
      pass_count++;
    end else begin
      `uvm_error("TEST", $sformatf("FAIL: Expected count 1, got %0d", phase.get_objection_count()))
      fail_count++;
    end

    // Test 6: Drop remaining objection
    `uvm_info("TEST", "Test 6: Drop remaining objection", UVM_LOW)
    phase.drop_objection(comp1, "comp1 done");
    if (phase.get_objection_count() == 0) begin
      `uvm_info("TEST", "PASS: Objection count is 0 after all drops", UVM_LOW)
      pass_count++;
    end else begin
      `uvm_error("TEST", $sformatf("FAIL: Expected count 0, got %0d", phase.get_objection_count()))
      fail_count++;
    end

    // Test 7: Check phase_done (should be true now)
    `uvm_info("TEST", "Test 7: Check phase_done after all objections dropped", UVM_LOW)
    if (phase.phase_done()) begin
      `uvm_info("TEST", "PASS: phase_done correctly returns 1 when all objections dropped", UVM_LOW)
      pass_count++;
    end else begin
      `uvm_error("TEST", "FAIL: phase_done should return 1 with no objections")
      fail_count++;
    end

    // Test 8: Test raise with count > 1
    `uvm_info("TEST", "Test 8: Raise with count=3", UVM_LOW)
    phase.raise_objection(this, "multi", 3);
    if (phase.get_objection_count() == 3) begin
      `uvm_info("TEST", "PASS: Objection count is 3 after raise(count=3)", UVM_LOW)
      pass_count++;
    end else begin
      `uvm_error("TEST", $sformatf("FAIL: Expected count 3, got %0d", phase.get_objection_count()))
      fail_count++;
    end

    // Test 9: Drop with count=3
    `uvm_info("TEST", "Test 9: Drop with count=3", UVM_LOW)
    phase.drop_objection(this, "multi done", 3);
    if (phase.phase_done()) begin
      `uvm_info("TEST", "PASS: Phase done after dropping count=3", UVM_LOW)
      pass_count++;
    end else begin
      `uvm_error("TEST", "FAIL: Phase should be done after dropping all")
      fail_count++;
    end

    // Summary
    `uvm_info("TEST", $sformatf("Test complete: %0d passed, %0d failed", pass_count, fail_count), UVM_LOW)

    if (fail_count == 0) begin
      `uvm_info("TEST", "All objection tests PASSED!", UVM_LOW)
    end else begin
      `uvm_error("TEST", "Some objection tests FAILED!")
    end
  endtask
endclass

//----------------------------------------------------------------------
// Top module
//----------------------------------------------------------------------
module t;
  initial begin
    objection_test test;
    uvm_phase phase;

    `uvm_info("TOP", "Starting UVM objection test", UVM_LOW)

    // Create test
    test = new("test", null);

    // Build phase
    phase = new("build");
    test.build_phase(phase);

    `uvm_info("TOP", "Build phase complete", UVM_LOW)

    // Run phase
    phase = new("run");
    test.run_phase(phase);

    $display("*-* All Finished *-*");
    $finish;
  end
endmodule
