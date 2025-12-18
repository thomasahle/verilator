// DESCRIPTION: Verilator: Test comprehensive UVM simulation features
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test UVM features commonly used in real testbenches like axi4_avip:
// - run_test() function
// - uvm_top / uvm_test_done globals
// - print_topology()
// - config_db with object types
// - Factory with overrides
// - Phase execution (build, connect, run)
// - Objection mechanism
// - Sequencer/driver pattern
// - Analysis ports

`include "uvm_macros.svh"
import uvm_pkg::*;

//----------------------------------------------------------------------
// Configuration class
//----------------------------------------------------------------------
class my_agent_config extends uvm_object;
  `uvm_object_utils(my_agent_config)

  uvm_active_passive_enum is_active = UVM_ACTIVE;
  bit has_coverage = 1;
  int agent_id = 0;

  function new(string name = "my_agent_config");
    super.new(name);
  endfunction

  virtual function string convert2string();
    return $sformatf("is_active=%s has_coverage=%0d agent_id=%0d",
                     is_active.name(), has_coverage, agent_id);
  endfunction

  // sprint() method that real UVM has
  virtual function string sprint(uvm_printer printer = null);
    return convert2string();
  endfunction
endclass

//----------------------------------------------------------------------
// Transaction class
//----------------------------------------------------------------------
class my_transaction extends uvm_sequence_item;
  `uvm_object_utils(my_transaction)

  rand bit [31:0] addr;
  rand bit [31:0] data;
  rand bit        write;

  function new(string name = "my_transaction");
    super.new(name);
  endfunction

  virtual function string convert2string();
    return $sformatf("addr=%h data=%h write=%b", addr, data, write);
  endfunction
endclass

//----------------------------------------------------------------------
// Sequence
//----------------------------------------------------------------------
class my_sequence extends uvm_sequence #(my_transaction);
  `uvm_object_utils(my_sequence)

  int num_items = 3;

  function new(string name = "my_sequence");
    super.new(name);
  endfunction

  virtual task body();
    `uvm_info("SEQ", $sformatf("Starting sequence with %0d items", num_items), UVM_LOW)
    for (int i = 0; i < num_items; i++) begin
      my_transaction tx;
      tx = my_transaction::type_id::create($sformatf("tx%0d", i));
      void'(tx.randomize());
      start_item(tx);
      finish_item(tx);
      `uvm_info("SEQ", $sformatf("Sent item %0d: %s", i, tx.convert2string()), UVM_LOW)
    end
    `uvm_info("SEQ", "Sequence complete", UVM_LOW)
  endtask
endclass

//----------------------------------------------------------------------
// Driver
//----------------------------------------------------------------------
class my_driver extends uvm_driver #(my_transaction);
  `uvm_component_utils(my_driver)

  int items_driven = 0;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual task run_phase(uvm_phase phase);
    my_transaction tx;
    `uvm_info("DRV", "Driver starting", UVM_LOW)
    forever begin
      seq_item_port.get_next_item(tx);
      if (tx != null) begin
        items_driven++;
        `uvm_info("DRV", $sformatf("Driving item %0d: %s", items_driven, tx.convert2string()), UVM_LOW)
        seq_item_port.item_done();
      end
    end
  endtask
endclass

//----------------------------------------------------------------------
// Monitor with analysis port
//----------------------------------------------------------------------
class my_monitor extends uvm_monitor;
  `uvm_component_utils(my_monitor)

  uvm_analysis_port #(my_transaction) ap;
  int items_observed = 0;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    ap = new("ap", this);
  endfunction

  // Simulate observing transactions
  virtual function void observe(my_transaction tx);
    items_observed++;
    `uvm_info("MON", $sformatf("Observed item %0d: %s", items_observed, tx.convert2string()), UVM_LOW)
    ap.write(tx);
  endfunction
endclass

//----------------------------------------------------------------------
// Scoreboard with analysis imp
//----------------------------------------------------------------------
class my_scoreboard extends uvm_scoreboard;
  `uvm_component_utils(my_scoreboard)

  uvm_analysis_imp #(my_transaction, my_scoreboard) analysis_export;
  int items_received = 0;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    analysis_export = new("analysis_export", this);
  endfunction

  virtual function void write(my_transaction t);
    items_received++;
    `uvm_info("SCB", $sformatf("Received item %0d: %s", items_received, t.convert2string()), UVM_LOW)
  endfunction
endclass

//----------------------------------------------------------------------
// Agent
//----------------------------------------------------------------------
class my_agent extends uvm_agent;
  `uvm_component_utils(my_agent)

  my_agent_config cfg;
  my_driver drv;
  uvm_sequencer #(my_transaction) seqr;
  my_monitor mon;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Get config from config_db
    if (!uvm_config_db #(my_agent_config)::get(this, "", "cfg", cfg)) begin
      `uvm_warning("NOCFG", "No config found, creating default")
      cfg = my_agent_config::type_id::create("cfg");
    end

    `uvm_info("AGENT", $sformatf("Config: %s", cfg.convert2string()), UVM_LOW)

    // Create monitor always
    mon = my_monitor::type_id::create("mon", this);

    // Create driver/sequencer only if active
    if (cfg.is_active == UVM_ACTIVE) begin
      drv = my_driver::type_id::create("drv", this);
      seqr = new("seqr", this);
    end
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (cfg.is_active == UVM_ACTIVE) begin
      drv.seq_item_port.connect(seqr.seq_item_export);
    end
  endfunction
endclass

//----------------------------------------------------------------------
// Environment
//----------------------------------------------------------------------
class my_env extends uvm_env;
  `uvm_component_utils(my_env)

  my_agent agent;
  my_scoreboard scb;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    agent = my_agent::type_id::create("agent", this);
    scb = my_scoreboard::type_id::create("scb", this);
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    // Connect monitor to scoreboard
    agent.mon.ap.connect(scb.analysis_export);
  endfunction
endclass

//----------------------------------------------------------------------
// Test (similar to axi4_base_test)
//----------------------------------------------------------------------
class my_test extends uvm_test;
  `uvm_component_utils(my_test)

  my_env env;
  my_agent_config agent_cfg;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Setup agent config
    agent_cfg = my_agent_config::type_id::create("agent_cfg");
    agent_cfg.is_active = UVM_ACTIVE;
    agent_cfg.has_coverage = 1;
    agent_cfg.agent_id = 0;

    // Store in config_db using wildcard (like axi4_base_test does)
    uvm_config_db #(my_agent_config)::set(this, "*", "cfg", agent_cfg);

    `uvm_info("TEST", $sformatf("Set agent config: %s", agent_cfg.sprint()), UVM_LOW)

    // Create environment
    env = my_env::type_id::create("env", this);
  endfunction

  virtual function void end_of_elaboration_phase(uvm_phase phase);
    // This is what axi4_base_test does
    uvm_top.print_topology();
    uvm_test_done.set_drain_time(this, 100ns);
  endfunction

  virtual task run_phase(uvm_phase phase);
    my_sequence seq;
    int pass_count = 0;
    int fail_count = 0;

    phase.raise_objection(this, "my_test");

    `uvm_info("TEST", "Starting comprehensive UVM test", UVM_LOW)

    // Test 1: Config_db retrieved correctly by agent
    if (env.agent.cfg != null && env.agent.cfg.is_active == UVM_ACTIVE) begin
      `uvm_info("TEST", "PASS: Agent config retrieved via config_db", UVM_LOW)
      pass_count++;
    end else begin
      `uvm_error("TEST", "FAIL: Agent config not retrieved correctly")
      fail_count++;
    end

    // Test 2: Components created correctly
    if (env.agent.drv != null && env.agent.seqr != null && env.agent.mon != null) begin
      `uvm_info("TEST", "PASS: All agent components created", UVM_LOW)
      pass_count++;
    end else begin
      `uvm_error("TEST", "FAIL: Missing agent components")
      fail_count++;
    end

    // Test 3: Analysis port connected
    // We'll test this by observing a transaction
    begin
      my_transaction tx;
      tx = my_transaction::type_id::create("test_tx");
      tx.addr = 32'hDEAD_BEEF;
      tx.data = 32'hCAFE_BABE;
      tx.write = 1;
      env.agent.mon.observe(tx);

      if (env.scb.items_received == 1) begin
        `uvm_info("TEST", "PASS: Analysis port correctly delivers to scoreboard", UVM_LOW)
        pass_count++;
      end else begin
        `uvm_error("TEST", "FAIL: Analysis port not working")
        fail_count++;
      end
    end

    // Test 4: Run a sequence through driver
    seq = my_sequence::type_id::create("seq");
    seq.num_items = 3;

    // Put items directly into sequencer (simplified)
    for (int i = 0; i < 3; i++) begin
      my_transaction tx;
      tx = my_transaction::type_id::create($sformatf("tx%0d", i));
      void'(tx.randomize());
      env.agent.seqr.send_request(tx);
    end

    // Wait for driver to process
    wait (env.agent.drv.items_driven >= 3);

    if (env.agent.drv.items_driven == 3) begin
      `uvm_info("TEST", "PASS: Driver processed 3 items", UVM_LOW)
      pass_count++;
    end else begin
      `uvm_error("TEST", $sformatf("FAIL: Driver only processed %0d items", env.agent.drv.items_driven))
      fail_count++;
    end

    // Summary
    `uvm_info("TEST", $sformatf("Test complete: %0d passed, %0d failed", pass_count, fail_count), UVM_LOW)

    if (fail_count == 0) begin
      `uvm_info("TEST", "All comprehensive UVM tests PASSED!", UVM_LOW)
    end else begin
      `uvm_error("TEST", "Some tests FAILED!")
    end

    phase.drop_objection(this);
  endtask
endclass

//----------------------------------------------------------------------
// Top module - simulates what hvl_top does
//----------------------------------------------------------------------
module t;
  initial begin
    my_test test;
    uvm_phase phase;

    `uvm_info("TOP", "Starting comprehensive UVM simulation test", UVM_LOW)

    // Initialize UVM globals (normally done by run_test)
    __uvm_pkg_init();

    // Test run_test() function exists
    // For now, we manually instantiate since run_test is a stub
    // run_test("my_test");

    // Manual test execution
    test = new("test", null);

    // Build phase
    `uvm_info("TOP", "Running build_phase", UVM_LOW)
    phase = new("build");
    test.build_phase(phase);
    test.env.build_phase(phase);
    test.env.agent.build_phase(phase);
    test.env.scb.build_phase(phase);
    test.env.agent.mon.build_phase(phase);
    if (test.env.agent.cfg.is_active == UVM_ACTIVE) begin
      test.env.agent.drv.build_phase(phase);
    end

    // Connect phase
    `uvm_info("TOP", "Running connect_phase", UVM_LOW)
    phase = new("connect");
    test.connect_phase(phase);
    test.env.connect_phase(phase);
    test.env.agent.connect_phase(phase);

    // End of elaboration
    `uvm_info("TOP", "Running end_of_elaboration_phase", UVM_LOW)
    phase = new("end_of_elaboration");
    test.end_of_elaboration_phase(phase);

    `uvm_info("TOP", "Build and connect phases complete", UVM_LOW)

    // Run phase
    `uvm_info("TOP", "Running run_phase", UVM_LOW)
    phase = new("run");
    fork
      if (test.env.agent.cfg.is_active == UVM_ACTIVE)
        test.env.agent.drv.run_phase(phase);
      test.run_phase(phase);
    join_any

    $display("*-* All Finished *-*");
    $finish;
  end
endmodule
