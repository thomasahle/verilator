// DESCRIPTION: Verilator: Test UVM run_phase objection mechanism
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test that run_phase ends when objections are dropped, even if
// some run_phase tasks have forever loops (like virtual sequences)

`include "uvm_macros.svh"
import uvm_pkg::*;

//----------------------------------------------------------------------
// Component with a forever loop in run_phase (like a slave responder)
//----------------------------------------------------------------------
class forever_component extends uvm_component;
  `uvm_component_utils(forever_component)
  int loop_count;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    loop_count = 0;
  endfunction

  virtual task run_phase(uvm_phase phase);
    // This forever loop simulates a slave sequence that runs continuously
    forever begin
      #10;
      loop_count++;
      if (loop_count % 10 == 0)
        `uvm_info("FOREVER", $sformatf("Loop count: %0d", loop_count), UVM_LOW)
    end
  endtask
endclass

//----------------------------------------------------------------------
// Component that raises and drops objection
//----------------------------------------------------------------------
class objection_component extends uvm_component;
  `uvm_component_utils(objection_component)
  int work_done;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    work_done = 0;
  endfunction

  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this, "objection_component starting");
    `uvm_info("OBJ", "Raised objection, starting work", UVM_LOW)

    // Do some work
    repeat (5) begin
      #100;
      work_done++;
      `uvm_info("OBJ", $sformatf("Work done: %0d", work_done), UVM_LOW)
    end

    `uvm_info("OBJ", "Dropping objection, work complete", UVM_LOW)
    phase.drop_objection(this, "objection_component done");
  endtask
endclass

//----------------------------------------------------------------------
// Test class
//----------------------------------------------------------------------
class objection_test extends uvm_test;
  `uvm_component_utils(objection_test)
  forever_component forever_comp;
  objection_component obj_comp;
  int pass_count;
  int fail_count;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
    pass_count = 0;
    fail_count = 0;
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("TEST", "Building test components", UVM_LOW)
    forever_comp = forever_component::type_id::create("forever_comp", this);
    obj_comp = objection_component::type_id::create("obj_comp", this);
  endfunction

  virtual task run_phase(uvm_phase phase);
    // Test's run_phase also raises an objection
    phase.raise_objection(this, "test starting");
    `uvm_info("TEST", "Test run_phase started", UVM_LOW)

    // Wait a bit, then drop objection
    #200;
    `uvm_info("TEST", "Test dropping objection", UVM_LOW)
    phase.drop_objection(this, "test done");
  endtask

  virtual function void report_phase(uvm_phase phase);
    super.report_phase(phase);

    `uvm_info("TEST", $sformatf("Forever comp loop count: %0d", forever_comp.loop_count), UVM_LOW)
    `uvm_info("TEST", $sformatf("Objection comp work done: %0d", obj_comp.work_done), UVM_LOW)

    // Check that forever loop ran for some time but stopped
    if (forever_comp.loop_count > 0 && forever_comp.loop_count < 1000) begin
      `uvm_info("TEST", "PASS: Forever loop ran but was stopped", UVM_LOW)
      pass_count++;
    end else begin
      `uvm_error("TEST", "FAIL: Forever loop count unexpected")
      fail_count++;
    end

    // Check that objection component completed its work
    if (obj_comp.work_done == 5) begin
      `uvm_info("TEST", "PASS: Objection component completed work", UVM_LOW)
      pass_count++;
    end else begin
      `uvm_error("TEST", $sformatf("FAIL: Objection component work_done=%0d, expected 5", obj_comp.work_done))
      fail_count++;
    end

    `uvm_info("TEST", $sformatf("Test complete: %0d passed, %0d failed", pass_count, fail_count), UVM_LOW)
    if (fail_count == 0) begin
      $write("*-* All Finished *-*\n");
    end
  endfunction
endclass

//----------------------------------------------------------------------
// Top module
//----------------------------------------------------------------------
module t;
  initial begin
    run_test("objection_test");
  end
endmodule
