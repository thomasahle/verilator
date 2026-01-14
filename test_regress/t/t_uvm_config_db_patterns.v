// DESCRIPTION: Verilator: Test UVM config_db pattern matching
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test config_db with various wildcard patterns

`include "uvm_macros.svh"
import uvm_pkg::*;

//----------------------------------------------------------------------
// Config classes
//----------------------------------------------------------------------
class my_config extends uvm_object;
  `uvm_object_utils(my_config)
  int value;
  function new(string name = "my_config");
    super.new(name);
  endfunction
endclass

//----------------------------------------------------------------------
// Child component that retrieves configs
//----------------------------------------------------------------------
class child_component extends uvm_component;
  `uvm_component_utils(child_component)
  my_config cfg;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(my_config)::get(this, "", "my_cfg", cfg)) begin
      `uvm_warning("CFG", $sformatf("Could not get my_cfg for %s", get_full_name()))
    end else begin
      `uvm_info("CFG", $sformatf("Got my_cfg for %s, value=%0d", get_full_name(), cfg.value), UVM_LOW)
    end
  endfunction
endclass

//----------------------------------------------------------------------
// Env component with children
//----------------------------------------------------------------------
class my_env extends uvm_env;
  `uvm_component_utils(my_env)
  child_component child1;
  child_component child2;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    child1 = child_component::type_id::create("child1", this);
    child2 = child_component::type_id::create("child2", this);
  endfunction
endclass

//----------------------------------------------------------------------
// Test class
//----------------------------------------------------------------------
class config_test extends uvm_test;
  `uvm_component_utils(config_test)
  my_env env_h;
  my_config cfg1, cfg2, cfg3, cfg4;
  int pass_count;
  int fail_count;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
    pass_count = 0;
    fail_count = 0;
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Create configs with different values
    cfg1 = new("cfg1"); cfg1.value = 100;
    cfg2 = new("cfg2"); cfg2.value = 200;
    cfg3 = new("cfg3"); cfg3.value = 300;
    cfg4 = new("cfg4"); cfg4.value = 400;

    // Test 1: Exact match - set config for specific path
    uvm_config_db#(my_config)::set(this, "env_h.child1", "my_cfg", cfg1);

    // Test 2: Wildcard suffix - set for all children of env
    // "*env*" pattern should match "env_h"
    uvm_config_db#(my_config)::set(this, "*env*.child2", "my_cfg", cfg2);

    // Create environment
    env_h = my_env::type_id::create("env_h", this);
  endfunction

  virtual function void report_phase(uvm_phase phase);
    super.report_phase(phase);

    // Check results
    if (env_h.child1.cfg != null && env_h.child1.cfg.value == 100) begin
      `uvm_info("TEST", "PASS: child1 got cfg with value 100", UVM_LOW)
      pass_count++;
    end else begin
      `uvm_error("TEST", "FAIL: child1 did not get expected cfg")
      fail_count++;
    end

    if (env_h.child2.cfg != null && env_h.child2.cfg.value == 200) begin
      `uvm_info("TEST", "PASS: child2 got cfg with value 200 (via *env* pattern)", UVM_LOW)
      pass_count++;
    end else begin
      `uvm_error("TEST", "FAIL: child2 did not get expected cfg (pattern matching issue)")
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
    run_test("config_test");
  end
endmodule
