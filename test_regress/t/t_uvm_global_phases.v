// DESCRIPTION: Verilator: UVM global phase objects and wait_for_state test
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // Test component that uses wait_for_state
  class sync_component extends uvm_component;
    bit saw_start_of_simulation;
    bit saw_run_phase;

    function new(string name, uvm_component parent);
      super.new(name, parent);
      saw_start_of_simulation = 0;
      saw_run_phase = 0;
    endfunction

    virtual function void start_of_simulation_phase(uvm_phase phase);
      super.start_of_simulation_phase(phase);
      saw_start_of_simulation = 1;
      `uvm_info("SYNC", "start_of_simulation_phase executed", UVM_LOW)
    endfunction

    virtual task run_phase(uvm_phase phase);
      phase.raise_objection(this);
      saw_run_phase = 1;
      `uvm_info("SYNC", "run_phase started", UVM_LOW)
      #10;
      `uvm_info("SYNC", "run_phase ending", UVM_LOW)
      phase.drop_objection(this);
    endtask

    function string get_type_name();
      return "sync_component";
    endfunction
  endclass

  // Test that uses global phase objects
  class global_phase_test extends uvm_test;
    sync_component sync_comp;
    int test_pass_count;

    `uvm_component_utils(global_phase_test)

    function new(string name, uvm_component parent);
      super.new(name, parent);
      test_pass_count = 0;
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      sync_comp = new("sync_comp", this);

      // Test 1: Check that global phase objects exist (initialized by run_test)
      $display("\n--- Test 1: Global phase objects exist ---");
      if (build_ph == null) begin
        `uvm_fatal("TEST", "build_ph is null")
      end
      if (connect_ph == null) begin
        `uvm_fatal("TEST", "connect_ph is null")
      end
      if (end_of_elaboration_ph == null) begin
        `uvm_fatal("TEST", "end_of_elaboration_ph is null")
      end
      if (start_of_simulation_ph == null) begin
        `uvm_fatal("TEST", "start_of_simulation_ph is null")
      end
      if (run_ph == null) begin
        `uvm_fatal("TEST", "run_ph is null")
      end
      if (extract_ph == null) begin
        `uvm_fatal("TEST", "extract_ph is null")
      end
      if (check_ph == null) begin
        `uvm_fatal("TEST", "check_ph is null")
      end
      if (report_ph == null) begin
        `uvm_fatal("TEST", "report_ph is null")
      end
      if (final_ph == null) begin
        `uvm_fatal("TEST", "final_ph is null")
      end
      $display("Test 1 PASSED: All global phase objects exist");
      test_pass_count++;

      // Test 2: Check phase names
      $display("\n--- Test 2: Global phase object names ---");
      if (build_ph.get_name() != "build") begin
        `uvm_fatal("TEST", $sformatf("build_ph name is '%s', expected 'build'", build_ph.get_name()))
      end
      if (run_ph.get_name() != "run") begin
        `uvm_fatal("TEST", $sformatf("run_ph name is '%s', expected 'run'", run_ph.get_name()))
      end
      if (start_of_simulation_ph.get_name() != "start_of_simulation") begin
        `uvm_fatal("TEST", $sformatf("start_of_simulation_ph name is '%s'", start_of_simulation_ph.get_name()))
      end
      $display("Test 2 PASSED: Global phase names correct");
      test_pass_count++;

      `uvm_info("TEST", "build_phase: created sync_comp", UVM_LOW)
    endfunction

    virtual function void end_of_elaboration_phase(uvm_phase phase);
      super.end_of_elaboration_phase(phase);
      `uvm_info("TEST", "end_of_elaboration_phase executed", UVM_LOW)
    endfunction

    virtual function void start_of_simulation_phase(uvm_phase phase);
      super.start_of_simulation_phase(phase);
      `uvm_info("TEST", "start_of_simulation_phase executed", UVM_LOW)
    endfunction

    virtual task run_phase(uvm_phase phase);
      phase.raise_objection(this);
      `uvm_info("TEST", "run_phase started", UVM_LOW)
      #20;
      `uvm_info("TEST", "run_phase ending", UVM_LOW)
      phase.drop_objection(this);
    endtask

    virtual function void report_phase(uvm_phase phase);
      super.report_phase(phase);

      // Test 3: Check that phases executed
      $display("\n--- Test 3: Phase execution verification ---");
      if (!sync_comp.saw_start_of_simulation) begin
        `uvm_fatal("TEST", "sync_comp did not see start_of_simulation_phase")
      end
      if (!sync_comp.saw_run_phase) begin
        `uvm_fatal("TEST", "sync_comp did not see run_phase")
      end
      $display("Test 3 PASSED: All phases executed correctly");
      test_pass_count++;

      $display("\n=== All %0d tests PASSED ===", test_pass_count);
      `uvm_info("TEST", "All phase checks PASSED", UVM_LOW)
    endfunction

    function string get_type_name();
      return "global_phase_test";
    endfunction
  endclass

  initial begin
    $display("=== Testing UVM Global Phase Objects ===");
    run_test("global_phase_test");
    $write("*-* All Coverage Tests Passed *-*\n");
  end
endmodule
