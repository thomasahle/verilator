// DESCRIPTION: Verilator: Test UVM print_topology functionality
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test print_topology() recursive printing

`include "uvm_macros.svh"

module t;
  import uvm_pkg::*;

  // Leaf component
  class leaf_comp extends uvm_component;
    `uvm_component_utils(leaf_comp)
    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction
  endclass

  // Middle component with children
  class middle_comp extends uvm_component;
    `uvm_component_utils(middle_comp)

    leaf_comp leaf1;
    leaf_comp leaf2;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      leaf1 = leaf_comp::type_id::create("leaf1", this);
      leaf2 = leaf_comp::type_id::create("leaf2", this);
    endfunction
  endclass

  // Top component
  class top_comp extends uvm_component;
    `uvm_component_utils(top_comp)

    middle_comp middle1;
    middle_comp middle2;
    leaf_comp   direct_leaf;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      middle1 = middle_comp::type_id::create("middle1", this);
      middle2 = middle_comp::type_id::create("middle2", this);
      direct_leaf = leaf_comp::type_id::create("direct_leaf", this);
    endfunction
  endclass

  // Test
  class test extends uvm_test;
    `uvm_component_utils(test)

    top_comp top;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      top = top_comp::type_id::create("top", this);
    endfunction

    virtual function void end_of_elaboration_phase(uvm_phase phase);
      super.end_of_elaboration_phase(phase);
      $display("\n=== Printing topology from test ===");
      print_topology();
      $display("\n=== Printing topology from top ===");
      top.print_topology();
      $display("\n=== Printing topology from middle1 ===");
      top.middle1.print_topology();
    endfunction

    virtual task run_phase(uvm_phase phase);
      phase.raise_objection(this);
      `uvm_info("TEST", "Topology test complete", UVM_LOW)
      phase.drop_objection(this);
    endtask

    virtual function void report_phase(uvm_phase phase);
      super.report_phase(phase);
      $write("*-* All Finished *-*\n");
    endfunction
  endclass

  initial begin
    run_test("test");
  end
endmodule
