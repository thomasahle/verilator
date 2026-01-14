// DESCRIPTION: Verilator: Test UVM driver-sequencer and analysis port patterns
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`include "uvm_macros.svh"
import uvm_pkg::*;

//----------------------------------------------------------------------
// Transaction class
//----------------------------------------------------------------------
class my_transaction extends uvm_sequence_item;
  `uvm_object_utils(my_transaction)

  rand bit [7:0] data;
  rand bit [3:0] addr;
  rand bit       wr_rd;  // 1 = write, 0 = read

  function new(string name = "my_transaction");
    super.new(name);
  endfunction

  virtual function string convert2string();
    return $sformatf("addr=%h data=%h wr_rd=%b", addr, data, wr_rd);
  endfunction

  virtual function void do_copy(uvm_object rhs);
    my_transaction rhs_t;
    super.do_copy(rhs);
    if ($cast(rhs_t, rhs)) begin
      data = rhs_t.data;
      addr = rhs_t.addr;
      wr_rd = rhs_t.wr_rd;
    end
  endfunction
endclass

//----------------------------------------------------------------------
// Sequence - generates transactions
//----------------------------------------------------------------------
class my_sequence extends uvm_sequence #(my_transaction);
  `uvm_object_utils(my_sequence)

  int num_items = 3;

  function new(string name = "my_sequence");
    super.new(name);
  endfunction

  virtual task body();
    `uvm_info("SEQ", $sformatf("Starting sequence, generating %0d items", num_items), UVM_LOW)
    for (int i = 0; i < num_items; i++) begin
      req = my_transaction::type_id::create($sformatf("req%0d", i));
      start_item(req);
      if (!req.randomize()) begin
        `uvm_warning("SEQ", "Randomization failed")
      end
      `uvm_info("SEQ", $sformatf("Generated item %0d: %s", i, req.convert2string()), UVM_LOW)
      finish_item(req);
    end
    `uvm_info("SEQ", "Sequence complete", UVM_LOW)
  endtask
endclass

//----------------------------------------------------------------------
// Monitor - observes bus and sends to analysis port
//----------------------------------------------------------------------
class my_monitor extends uvm_monitor;
  `uvm_component_utils(my_monitor)

  uvm_analysis_port #(my_transaction) ap;
  int items_observed = 0;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
    ap = new("ap", this);
  endfunction

  // Method to simulate observing a transaction
  virtual function void observe(my_transaction t);
    items_observed++;
    `uvm_info("MON", $sformatf("Observed item %0d: %s", items_observed, t.convert2string()), UVM_LOW)
    ap.write(t);  // Send to analysis port subscribers
  endfunction
endclass

//----------------------------------------------------------------------
// Scoreboard - receives transactions via analysis export
//----------------------------------------------------------------------
class my_scoreboard extends uvm_scoreboard;
  `uvm_component_utils(my_scoreboard)

  uvm_analysis_imp #(my_transaction, my_scoreboard) analysis_export;
  my_transaction received_items[$];

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
    analysis_export = new("analysis_export", this);
  endfunction

  // This function is called when analysis_imp receives a write
  virtual function void write(my_transaction t);
    received_items.push_back(t);
    `uvm_info("SCB", $sformatf("Scoreboard received item %0d: %s",
              received_items.size(), t.convert2string()), UVM_LOW)
  endfunction

  function int get_count();
    return received_items.size();
  endfunction
endclass

//----------------------------------------------------------------------
// Coverage subscriber - demonstrates uvm_subscriber pattern
//----------------------------------------------------------------------
class my_coverage extends uvm_subscriber #(my_transaction);
  `uvm_component_utils(my_coverage)

  int items_covered = 0;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void write(my_transaction t);
    items_covered++;
    `uvm_info("COV", $sformatf("Coverage collected item %0d: %s",
              items_covered, t.convert2string()), UVM_LOW)
  endfunction

  function int get_count();
    return items_covered;
  endfunction
endclass

//----------------------------------------------------------------------
// Agent - contains monitor
//----------------------------------------------------------------------
class my_agent extends uvm_agent;
  `uvm_component_utils(my_agent)

  my_monitor mon;
  uvm_sequencer #(my_transaction) seqr;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    mon = my_monitor::type_id::create("mon", this);
    seqr = new("seqr", this);
  endfunction
endclass

//----------------------------------------------------------------------
// Environment
//----------------------------------------------------------------------
class my_env extends uvm_env;
  `uvm_component_utils(my_env)

  my_agent agent;
  my_scoreboard scb;
  my_coverage cov;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    agent = my_agent::type_id::create("agent", this);
    scb = my_scoreboard::type_id::create("scb", this);
    cov = my_coverage::type_id::create("cov", this);
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    // Connect monitor's analysis port to scoreboard and coverage
    agent.mon.ap.connect(scb.analysis_export);
    agent.mon.ap.connect(cov.analysis_export);
  endfunction
endclass

//----------------------------------------------------------------------
// Test
//----------------------------------------------------------------------
class my_test extends uvm_test;
  `uvm_component_utils(my_test)

  my_env env;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env = my_env::type_id::create("env", this);
  endfunction

  virtual task run_phase(uvm_phase phase);
    `uvm_info("TEST", "Starting analysis port test", UVM_LOW)

    // Simulate the monitor observing transactions (no delays needed for unit test)
    for (int i = 0; i < 3; i++) begin
      my_transaction observed_tx;
      observed_tx = my_transaction::type_id::create($sformatf("obs%0d", i));
      void'(observed_tx.randomize());
      env.agent.mon.observe(observed_tx);
    end

    // Check results
    `uvm_info("TEST", $sformatf("Monitor observed %0d items", env.agent.mon.items_observed), UVM_LOW)
    `uvm_info("TEST", $sformatf("Scoreboard received %0d items", env.scb.get_count()), UVM_LOW)
    `uvm_info("TEST", $sformatf("Coverage collected %0d items", env.cov.get_count()), UVM_LOW)

    if (env.scb.get_count() == 3 && env.cov.get_count() == 3) begin
      `uvm_info("TEST", "Analysis port pattern working correctly!", UVM_LOW)
    end else begin
      `uvm_error("TEST", "Analysis port pattern failed!")
    end

    `uvm_info("TEST", "Test complete", UVM_LOW)
  endtask
endclass

//----------------------------------------------------------------------
// Top module
//----------------------------------------------------------------------
module t;
  initial begin
    my_test test;
    uvm_phase phase;

    `uvm_info("TOP", "Starting UVM analysis port test", UVM_LOW)

    // Create test
    test = new("test", null);

    // Build phase
    phase = new("build");
    test.build_phase(phase);
    test.env.build_phase(phase);
    test.env.agent.build_phase(phase);
    test.env.scb.build_phase(phase);
    test.env.cov.build_phase(phase);

    // Connect phase
    phase = new("connect");
    test.connect_phase(phase);
    test.env.connect_phase(phase);
    test.env.agent.connect_phase(phase);

    `uvm_info("TOP", "Build and connect phases complete", UVM_LOW)

    // Run phase
    phase = new("run");
    test.run_phase(phase);

    $display("*-* All Finished *-*");
    $finish;
  end
endmodule
