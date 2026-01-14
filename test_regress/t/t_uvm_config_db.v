// DESCRIPTION: Verilator: Test uvm_config_db functionality
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`include "uvm_macros.svh"
import uvm_pkg::*;

//----------------------------------------------------------------------
// Config class
//----------------------------------------------------------------------
class my_config extends uvm_object;
  `uvm_object_utils(my_config)
  int value;

  function new(string name = "my_config");
    super.new(name);
    value = 0;
  endfunction
endclass

//----------------------------------------------------------------------
// Child component
//----------------------------------------------------------------------
class my_child extends uvm_component;
  `uvm_component_utils(my_child)
  my_config cfg;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("CHILD", "build_phase - trying to get config", UVM_LOW)
    if (!uvm_config_db#(my_config)::get(this, "", "my_config", cfg)) begin
      `uvm_error("CHILD", "Failed to get my_config from config_db")
    end else begin
      `uvm_info("CHILD", $sformatf("Got config with value = %0d", cfg.value), UVM_LOW)
    end
  endfunction
endclass

//----------------------------------------------------------------------
// Test class
//----------------------------------------------------------------------
class config_test extends uvm_test;
  `uvm_component_utils(config_test)
  my_child child;
  my_config cfg;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("TEST", "build_phase - creating config", UVM_LOW)
    cfg = new("my_config");
    cfg.value = 42;
    // Set config for all descendants using wildcard
    uvm_config_db#(my_config)::set(this, "*", "my_config", cfg);
    `uvm_info("TEST", $sformatf("Set config with value = %0d", cfg.value), UVM_LOW)
    // Create child
    child = my_child::type_id::create("child", this);
  endfunction

  virtual function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    if (child.cfg != null && child.cfg.value == 42) begin
      `uvm_info("TEST", "Config propagated correctly!", UVM_LOW)
      $write("*-* All Finished *-*\n");
    end else begin
      `uvm_error("TEST", "Config did NOT propagate correctly")
    end
  endfunction
endclass

//----------------------------------------------------------------------
// Top module
//----------------------------------------------------------------------
module t;
  initial begin
    run_test("config_test");
  end
endmodule
