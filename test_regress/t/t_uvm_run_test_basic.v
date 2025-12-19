// DESCRIPTION: Verilator: Test UVM run_test() basic flow
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test basic UVM run_test() flow with factory registration

`include "uvm_macros.svh"
import uvm_pkg::*;

//----------------------------------------------------------------------
// Simple test class
//----------------------------------------------------------------------
class basic_test extends uvm_test;
  `uvm_component_utils(basic_test)

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("TEST", "build_phase called", UVM_LOW)
  endfunction

  virtual task run_phase(uvm_phase phase);
    `uvm_info("TEST", "run_phase started", UVM_LOW)
    `uvm_info("TEST", "run_phase finished", UVM_LOW)
    // Drop objection immediately (no work to do in this basic test)
    phase.drop_objection(this, "Ending test");
  endtask

  virtual function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    `uvm_info("TEST", "report_phase - All Finished", UVM_LOW)
    $write("*-* All Finished *-*\n");
  endfunction
endclass

//----------------------------------------------------------------------
// Top module - uses run_test()
//----------------------------------------------------------------------
module t;
  initial begin
    $display("Starting run_test...");
    run_test("basic_test");
    $display("run_test completed");
  end
endmodule
