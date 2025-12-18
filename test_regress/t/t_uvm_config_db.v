// DESCRIPTION: Verilator: Test UVM config_db with virtual interfaces
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`include "uvm_macros.svh"
import uvm_pkg::*;

// Simple interface for testing
interface simple_if;
  logic clk;
  logic [7:0] data;
  logic valid;

  modport master_mp(output data, output valid, input clk);
  modport slave_mp(input data, input valid, input clk);
endinterface

// Driver that uses virtual interface from config_db
class my_driver extends uvm_driver #(uvm_sequence_item);
  `uvm_component_utils(my_driver)

  virtual simple_if vif;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // Get virtual interface from config_db
    if (!uvm_config_db #(virtual simple_if)::get(this, "", "vif", vif)) begin
      `uvm_warning("NOVIF", "Virtual interface not found in config_db")
    end else begin
      `uvm_info("DRV", "Got virtual interface from config_db", UVM_LOW)
    end
  endfunction

  virtual task run_phase(uvm_phase phase);
    `uvm_info("DRV", "Driver running", UVM_LOW)
  endtask
endclass

// Monitor that uses virtual interface
class my_monitor extends uvm_monitor;
  `uvm_component_utils(my_monitor)

  virtual simple_if.slave_mp vif;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // Get virtual interface modport from config_db
    if (!uvm_config_db #(virtual simple_if.slave_mp)::get(this, "", "vif", vif)) begin
      `uvm_warning("NOVIF", "Virtual interface modport not found in config_db")
    end else begin
      `uvm_info("MON", "Got virtual interface modport from config_db", UVM_LOW)
    end
  endfunction
endclass

// Agent containing driver and monitor
class my_agent extends uvm_agent;
  `uvm_component_utils(my_agent)

  my_driver drv;
  my_monitor mon;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    drv = my_driver::type_id::create("drv", this);
    drv.build_phase(phase);
    mon = my_monitor::type_id::create("mon", this);
    mon.build_phase(phase);
  endfunction
endclass

// Environment
class my_env extends uvm_env;
  `uvm_component_utils(my_env)

  my_agent agent;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    agent = my_agent::type_id::create("agent", this);
    agent.build_phase(phase);
  endfunction
endclass

// Test
class my_test extends uvm_test;
  `uvm_component_utils(my_test)

  my_env env;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env = my_env::type_id::create("env", this);
    env.build_phase(phase);
  endfunction

  virtual task run_phase(uvm_phase phase);
    `uvm_info("TEST", "Test running - virtual interface config_db test", UVM_LOW)
    `uvm_info("TEST", "Test complete", UVM_LOW)
  endtask
endclass

// Top module
module t;
  // Instantiate the interface
  simple_if my_if();

  // Generate clock (limited iterations)
  initial begin
    my_if.clk = 0;
    repeat(20) #5 my_if.clk = ~my_if.clk;
  end

  // Test
  initial begin
    my_test test;
    uvm_phase phase;

    // Store virtual interface in config_db (stub - just tests compilation)
    uvm_config_db #(virtual simple_if)::set(null, "*", "vif", my_if);
    uvm_config_db #(virtual simple_if.slave_mp)::set(null, "*", "vif", my_if.slave_mp);

    `uvm_info("TOP", "Starting config_db virtual interface test", UVM_LOW)

    // Create and run test
    test = new("test", null);
    phase = new("build");
    test.build_phase(phase);

    `uvm_info("TOP", "Build phase complete - virtual interface config_db compiles correctly", UVM_LOW)

    // Run phase
    phase = new("run");
    test.run_phase(phase);

    // Test passes - the key thing is that config_db with virtual interfaces compiles
    $display("*-* All Finished *-*");
    $finish;
  end
endmodule
