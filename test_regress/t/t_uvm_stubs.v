// DESCRIPTION: Verilator: Verilog Test module for UVM stub library
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`include "uvm_macros.svh"
import uvm_pkg::*;

// Simple transaction class
class my_transaction extends uvm_sequence_item;
  `uvm_object_utils(my_transaction)

  rand bit [7:0] data;
  rand bit [3:0] addr;

  function new(string name = "my_transaction");
    super.new(name);
  endfunction

  virtual function string convert2string();
    return $sformatf("addr=%h data=%h", addr, data);
  endfunction
endclass

// Simple sequence
class my_sequence extends uvm_sequence #(my_transaction);
  `uvm_object_utils(my_sequence)

  function new(string name = "my_sequence");
    super.new(name);
  endfunction

  virtual task body();
    req = new("req");
    void'(req.randomize());
    `uvm_info("SEQ", $sformatf("Generated: %s", req.convert2string()), UVM_LOW)
  endtask
endclass

// Simple driver
class my_driver extends uvm_driver #(my_transaction);
  `uvm_component_utils(my_driver)

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual task run_phase(uvm_phase phase);
    `uvm_info("DRV", "Driver running", UVM_LOW)
  endtask
endclass

// Simple monitor with analysis port
class my_monitor extends uvm_monitor;
  `uvm_component_utils(my_monitor)

  uvm_analysis_port #(my_transaction) ap;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
    ap = new("ap", this);
  endfunction

  virtual task run_phase(uvm_phase phase);
    my_transaction tx = new("tx");
    `uvm_info("MON", "Monitor running", UVM_LOW)
    ap.write(tx);
  endtask
endclass

// Simple agent
class my_agent extends uvm_agent;
  `uvm_component_utils(my_agent)

  my_driver drv;
  my_monitor mon;
  uvm_sequencer #(my_transaction) seqr;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (is_active == UVM_ACTIVE) begin
      drv = my_driver::type_id::create("drv", this);
      seqr = new("seqr", this);
    end
    mon = my_monitor::type_id::create("mon", this);
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (is_active == UVM_ACTIVE) begin
      drv.seq_item_port.connect(seqr.seq_item_export);
    end
  endfunction
endclass

// Simple environment
class my_env extends uvm_env;
  `uvm_component_utils(my_env)

  my_agent agent;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    agent = my_agent::type_id::create("agent", this);
    agent.build_phase(phase);  // Propagate build phase
  endfunction
endclass

// Simple test
class my_test extends uvm_test;
  `uvm_component_utils(my_test)

  my_env env;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env = my_env::type_id::create("env", this);
    env.build_phase(phase);  // Propagate build phase
  endfunction

  virtual task run_phase(uvm_phase phase);
    my_sequence seq;
    seq = my_sequence::type_id::create("seq");
    `uvm_info("TEST", "Starting test", UVM_LOW)
    seq.start(env.agent.seqr);
    `uvm_info("TEST", "Test complete", UVM_LOW)
  endtask
endclass

// Test TLM FIFOs
class fifo_test extends uvm_object;
  uvm_tlm_fifo #(my_transaction) tlm_fifo;
  uvm_tlm_analysis_fifo #(my_transaction) analysis_fifo;

  function new(string name = "fifo_test");
    super.new(name);
    tlm_fifo = new("tlm_fifo", null, 10);
    analysis_fifo = new("analysis_fifo", null);
  endfunction

  function void run();
    my_transaction tx, rx;

    // Test TLM FIFO
    tx = new("tx1");
    tx.data = 8'hAB;
    tx.addr = 4'h5;

    if (tlm_fifo.try_put(tx)) begin
      $display("[FIFO] Put transaction: %s", tx.convert2string());
    end

    if (tlm_fifo.try_get(rx)) begin
      $display("[FIFO] Got transaction: %s", rx.convert2string());
      if (rx.data != 8'hAB || rx.addr != 4'h5) begin
        $display("%%Error: FIFO data mismatch");
        $stop;
      end
    end

    // Test analysis FIFO
    tx = new("tx2");
    tx.data = 8'hCD;
    analysis_fifo.write(tx);
    $display("[FIFO] Analysis FIFO size: %0d", analysis_fifo.size());

    if (analysis_fifo.size() != 1) begin
      $display("%%Error: Analysis FIFO size mismatch");
      $stop;
    end
  endfunction
endclass

module t;
  initial begin
    my_test test;
    fifo_test ft;

    // Test UVM messaging
    `uvm_info("TOP", "Testing UVM info macro", UVM_LOW)
    `uvm_warning("TOP", "Testing UVM warning macro")

    // Test factory creation
    test = my_test::type_id::create("test", null);
    $display("[TOP] Created test: %s", test.get_name());

    // Test build phase
    test.build_phase(null);
    $display("[TOP] Build phase complete");

    // Test FIFO operations
    ft = new("ft");
    ft.run();

    // Test run phase (sequential for simplicity)
    test.run_phase(null);

    $display("*-* All Coverage *-*");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
