// DESCRIPTION: Verilator: Test UVM run_test() with factory registration
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test that run_test() can create a test from the factory and run UVM phases

`include "uvm_macros.svh"

package test_pkg;

  import uvm_pkg::*;

  //----------------------------------------------------------------------
  // Simple test class
  //----------------------------------------------------------------------
  class simple_test extends uvm_test;
    `uvm_component_utils(simple_test)

    int build_count = 0;
    int connect_count = 0;
    int run_count = 0;

    function new(string name = "simple_test", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      build_count++;
      $display("[TEST] build_phase executed");
    endfunction

    virtual function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      connect_count++;
      $display("[TEST] connect_phase executed");
    endfunction

    virtual task run_phase(uvm_phase phase);
      super.run_phase(phase);
      run_count++;
      $display("[TEST] run_phase started @ %0t", $time);
      phase.raise_objection(this, "Running test");
      $display("[TEST] objection raised, count=%0d", phase.get_objection_count(this));

      // Simulate some work
      #10;
      $display("[TEST] run_phase work done @ %0t", $time);

      phase.drop_objection(this, "Test complete");
      $display("[TEST] objection dropped, count=%0d, phase_done=%0d", phase.get_objection_count(this), phase.phase_done());
      $display("[TEST] run_phase ended @ %0t", $time);
    endtask

    virtual function void report_phase(uvm_phase phase);
      super.report_phase(phase);
      $display("[TEST] report_phase: build_count=%0d connect_count=%0d run_count=%0d",
               build_count, connect_count, run_count);

      // Verify phases were called
      if (build_count == 1 && connect_count == 1 && run_count == 1) begin
        $display("*-* All Finished *-*");
      end else begin
        $display("%%Error: Phase counts wrong");
        $stop;
      end
    endfunction

  endclass

endpackage

module t;
  import uvm_pkg::*;
  import test_pkg::*;

  initial begin
    // Register the test with the factory
    simple_test::type_id::register();

    // Run the test via factory
    run_test("simple_test");
  end

endmodule
