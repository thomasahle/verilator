// DESCRIPTION: Verilator: Test UVM config_db functional storage/retrieval
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`include "uvm_macros.svh"
import uvm_pkg::*;

//----------------------------------------------------------------------
// Configuration class for testing
//----------------------------------------------------------------------
class my_config extends uvm_object;
  `uvm_object_utils(my_config)

  int data_width = 32;
  int addr_width = 16;
  bit enable_coverage = 1;

  function new(string name = "my_config");
    super.new(name);
  endfunction

  virtual function string convert2string();
    return $sformatf("data_width=%0d addr_width=%0d enable_coverage=%0b",
                     data_width, addr_width, enable_coverage);
  endfunction
endclass

//----------------------------------------------------------------------
// Agent that retrieves config from config_db
//----------------------------------------------------------------------
class my_agent extends uvm_agent;
  `uvm_component_utils(my_agent)

  my_config cfg;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // Try to get config from config_db
    if (!uvm_config_db #(my_config)::get(this, "", "cfg", cfg)) begin
      `uvm_warning("NOCFG", "Config not found in config_db, using defaults")
      cfg = my_config::type_id::create("cfg");
    end else begin
      `uvm_info("AGENT", $sformatf("Got config from config_db: %s", cfg.convert2string()), UVM_LOW)
    end
  endfunction
endclass

//----------------------------------------------------------------------
// Environment that sets and gets configs
//----------------------------------------------------------------------
class my_env extends uvm_env;
  `uvm_component_utils(my_env)

  my_agent agent;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    agent = my_agent::type_id::create("agent", this);
  endfunction
endclass

//----------------------------------------------------------------------
// Test
//----------------------------------------------------------------------
class my_test extends uvm_test;
  `uvm_component_utils(my_test)

  my_env env;
  my_config test_cfg;
  int test_int;
  string test_str;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Create and configure
    test_cfg = my_config::type_id::create("test_cfg");
    test_cfg.data_width = 64;
    test_cfg.addr_width = 32;
    test_cfg.enable_coverage = 0;

    // Store in config_db with wildcard pattern
    uvm_config_db #(my_config)::set(this, "*", "cfg", test_cfg);
    `uvm_info("TEST", $sformatf("Set config in config_db: %s", test_cfg.convert2string()), UVM_LOW)

    // Also test basic types
    uvm_config_db #(int)::set(null, "*", "test_int", 42);
    uvm_config_db #(string)::set(null, "*", "test_str", "hello_world");

    // Create environment
    env = my_env::type_id::create("env", this);
  endfunction

  virtual task run_phase(uvm_phase phase);
    int retrieved_int;
    string retrieved_str;
    my_config retrieved_cfg;
    int pass_count = 0;
    int fail_count = 0;

    `uvm_info("TEST", "Starting config_db functional test", UVM_LOW)

    // Test 1: Retrieve int value
    if (uvm_config_db #(int)::get(null, "*", "test_int", retrieved_int)) begin
      if (retrieved_int == 42) begin
        `uvm_info("TEST", $sformatf("PASS: Retrieved int value = %0d", retrieved_int), UVM_LOW)
        pass_count++;
      end else begin
        `uvm_error("TEST", $sformatf("FAIL: Expected int 42, got %0d", retrieved_int))
        fail_count++;
      end
    end else begin
      `uvm_error("TEST", "FAIL: Could not retrieve int from config_db")
      fail_count++;
    end

    // Test 2: Retrieve string value
    if (uvm_config_db #(string)::get(null, "*", "test_str", retrieved_str)) begin
      if (retrieved_str == "hello_world") begin
        `uvm_info("TEST", $sformatf("PASS: Retrieved string value = '%s'", retrieved_str), UVM_LOW)
        pass_count++;
      end else begin
        `uvm_error("TEST", $sformatf("FAIL: Expected string 'hello_world', got '%s'", retrieved_str))
        fail_count++;
      end
    end else begin
      `uvm_error("TEST", "FAIL: Could not retrieve string from config_db")
      fail_count++;
    end

    // Test 3: Check that agent got the config (via wildcard)
    if (env.agent.cfg != null) begin
      if (env.agent.cfg.data_width == 64 && env.agent.cfg.addr_width == 32) begin
        `uvm_info("TEST", "PASS: Agent received correct config via wildcard", UVM_LOW)
        pass_count++;
      end else begin
        `uvm_error("TEST", $sformatf("FAIL: Agent config mismatch: %s", env.agent.cfg.convert2string()))
        fail_count++;
      end
    end else begin
      `uvm_error("TEST", "FAIL: Agent config is null")
      fail_count++;
    end

    // Test 4: Test exists() function
    if (uvm_config_db #(int)::exists(null, "*", "test_int")) begin
      `uvm_info("TEST", "PASS: exists() correctly found test_int", UVM_LOW)
      pass_count++;
    end else begin
      `uvm_error("TEST", "FAIL: exists() did not find test_int")
      fail_count++;
    end

    // Summary
    `uvm_info("TEST", $sformatf("Test complete: %0d passed, %0d failed", pass_count, fail_count), UVM_LOW)

    if (fail_count == 0) begin
      `uvm_info("TEST", "All config_db tests PASSED!", UVM_LOW)
    end else begin
      `uvm_error("TEST", "Some config_db tests FAILED!")
    end
  endtask
endclass

//----------------------------------------------------------------------
// Top module
//----------------------------------------------------------------------
module t;
  initial begin
    my_test test;
    uvm_phase phase;

    `uvm_info("TOP", "Starting UVM config_db functional test", UVM_LOW)

    // Create test
    test = new("test", null);

    // Build phase
    phase = new("build");
    test.build_phase(phase);
    test.env.build_phase(phase);
    test.env.agent.build_phase(phase);

    `uvm_info("TOP", "Build phase complete", UVM_LOW)

    // Run phase
    phase = new("run");
    test.run_phase(phase);

    $display("*-* All Finished *-*");
    $finish;
  end
endmodule
