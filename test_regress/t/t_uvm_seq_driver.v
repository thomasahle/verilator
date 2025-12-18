// DESCRIPTION: Verilator: Test UVM driver-sequencer handshake pattern
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`include "uvm_macros.svh"
import uvm_pkg::*;

//----------------------------------------------------------------------
// Simple transaction class
//----------------------------------------------------------------------
class simple_tx extends uvm_sequence_item;
  `uvm_object_utils(simple_tx)

  rand bit [7:0] data;
  int id;

  function new(string name = "simple_tx");
    super.new(name);
  endfunction

  virtual function string convert2string();
    return $sformatf("id=%0d data=%h", id, data);
  endfunction
endclass

//----------------------------------------------------------------------
// Simple sequence - creates and sends transactions
//----------------------------------------------------------------------
class simple_seq extends uvm_sequence #(simple_tx);
  `uvm_object_utils(simple_seq)

  int num_items = 3;

  function new(string name = "simple_seq");
    super.new(name);
  endfunction

  virtual task body();
    `uvm_info("SEQ", $sformatf("Starting sequence, generating %0d items", num_items), UVM_LOW)
    for (int i = 0; i < num_items; i++) begin
      simple_tx tx;
      tx = simple_tx::type_id::create($sformatf("tx%0d", i));
      tx.id = i;
      void'(tx.randomize());

      // Standard UVM sequence handshake
      start_item(tx);
      `uvm_info("SEQ", $sformatf("Sending item %0d: %s", i, tx.convert2string()), UVM_LOW)
      finish_item(tx);
    end
    `uvm_info("SEQ", "Sequence complete", UVM_LOW)
  endtask
endclass

//----------------------------------------------------------------------
// Simple driver - gets transactions from sequencer
//----------------------------------------------------------------------
class simple_driver extends uvm_driver #(simple_tx);
  `uvm_component_utils(simple_driver)

  int items_driven = 0;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual task run_phase(uvm_phase phase);
    simple_tx tx;

    `uvm_info("DRV", "Driver starting", UVM_LOW)

    // Driver loop - get items and process them
    forever begin
      // Get next item from sequencer
      seq_item_port.get_next_item(tx);

      if (tx != null) begin
        items_driven++;
        `uvm_info("DRV", $sformatf("Driving item %0d: %s", items_driven, tx.convert2string()), UVM_LOW)

        // Signal completion
        seq_item_port.item_done();
      end
    end
  endtask

  function int get_count();
    return items_driven;
  endfunction
endclass

//----------------------------------------------------------------------
// Simple agent - contains driver and sequencer
//----------------------------------------------------------------------
class simple_agent extends uvm_agent;
  `uvm_component_utils(simple_agent)

  simple_driver drv;
  uvm_sequencer #(simple_tx) seqr;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    drv = simple_driver::type_id::create("drv", this);
    seqr = new("seqr", this);
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    // Connect driver's seq_item_port to sequencer's seq_item_export
    drv.seq_item_port.connect(seqr.seq_item_export);
  endfunction
endclass

//----------------------------------------------------------------------
// Test
//----------------------------------------------------------------------
class simple_test extends uvm_test;
  `uvm_component_utils(simple_test)

  simple_agent agent;
  simple_seq seq;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    agent = simple_agent::type_id::create("agent", this);
    seq = simple_seq::type_id::create("seq");
  endfunction

  virtual task run_phase(uvm_phase phase);
    `uvm_info("TEST", "Starting driver-sequencer handshake test", UVM_LOW)

    // Put some items in the sequencer's FIFO using public send_request() method
    for (int i = 0; i < 3; i++) begin
      simple_tx tx;
      tx = simple_tx::type_id::create($sformatf("tx%0d", i));
      tx.id = i;
      void'(tx.randomize());
      `uvm_info("TEST", $sformatf("Sending item %0d to sequencer: %s", i, tx.convert2string()), UVM_LOW)
      agent.seqr.send_request(tx);
    end

    // Let the driver process items (driver is in forever loop, so we just wait)
    // Wait for driver to process all items
    wait (agent.drv.get_count() >= 3);

    // Check results
    `uvm_info("TEST", $sformatf("Driver processed %0d items", agent.drv.get_count()), UVM_LOW)

    if (agent.drv.get_count() == 3) begin
      `uvm_info("TEST", "Driver-sequencer handshake working correctly!", UVM_LOW)
    end else begin
      `uvm_error("TEST", "Driver-sequencer handshake failed!")
    end

    `uvm_info("TEST", "Test complete", UVM_LOW)
  endtask
endclass

//----------------------------------------------------------------------
// Top module
//----------------------------------------------------------------------
module t;
  initial begin
    simple_test test;
    uvm_phase phase;

    `uvm_info("TOP", "Starting UVM driver-sequencer handshake test", UVM_LOW)

    // Create test
    test = new("test", null);

    // Build phase
    phase = new("build");
    test.build_phase(phase);
    test.agent.build_phase(phase);
    test.agent.drv.build_phase(phase);
    test.agent.seqr.build_phase(phase);

    // Connect phase
    phase = new("connect");
    test.connect_phase(phase);
    test.agent.connect_phase(phase);

    `uvm_info("TOP", "Build and connect phases complete", UVM_LOW)

    // Run phase - start driver and test in parallel
    phase = new("run");
    fork
      test.agent.drv.run_phase(phase);
      test.run_phase(phase);
    join_any

    $display("*-* All Finished *-*");
    $finish;
  end
endmodule
