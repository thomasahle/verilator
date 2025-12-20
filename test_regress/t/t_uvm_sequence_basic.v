// DESCRIPTION: Verilator: Test for UVM sequence support
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // Simple transaction class
  class my_transaction extends uvm_sequence_item;
    rand bit [7:0] data;
    rand bit [3:0] addr;

    `uvm_object_utils(my_transaction)

    function new(string name = "my_transaction");
      super.new(name);
    endfunction

    virtual function string convert2string();
      return $sformatf("addr=%0h data=%0h", addr, data);
    endfunction
  endclass

  // Simple driver that processes items
  class my_driver extends uvm_component;
    uvm_seq_item_pull_port #(my_transaction) seq_item_port;
    int item_count;

    `uvm_component_utils(my_driver)

    function new(string name = "", uvm_component parent = null);
      super.new(name, parent);
      item_count = 0;
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      seq_item_port = new("seq_item_port", this);
    endfunction

    virtual task run_phase(uvm_phase phase);
      my_transaction req;
      forever begin
        seq_item_port.get_next_item(req);
        `uvm_info("DRV", $sformatf("Got item %0d: %s", item_count, req.convert2string()), UVM_MEDIUM)
        #10;  // Simulate some processing time
        item_count++;
        seq_item_port.item_done();
      end
    endtask
  endclass

  // Custom sequencer (to test p_sequencer)
  class my_sequencer extends uvm_sequencer #(my_transaction);
    int custom_field;

    `uvm_component_utils(my_sequencer)

    function new(string name = "", uvm_component parent = null);
      super.new(name, parent);
      custom_field = 42;
    endfunction
  endclass

  // Simple sequence that uses uvm_do macro
  class my_sequence extends uvm_sequence #(my_transaction);
    `uvm_object_utils(my_sequence)
    `uvm_declare_p_sequencer(my_sequencer)

    int num_items;

    function new(string name = "my_sequence");
      super.new(name);
      num_items = 3;
    endfunction

    virtual task body();
      `uvm_info("SEQ", $sformatf("Starting sequence, p_sequencer.custom_field=%0d", p_sequencer.custom_field), UVM_MEDIUM)

      for (int i = 0; i < num_items; i++) begin
        `uvm_do(req)
        `uvm_info("SEQ", $sformatf("Sent item %0d: %s", i, req.convert2string()), UVM_MEDIUM)
      end

      `uvm_info("SEQ", "Sequence complete", UVM_MEDIUM)
    endtask
  endclass

  // Agent containing driver and sequencer
  class my_agent extends uvm_component;
    my_driver drv;
    my_sequencer sqr;

    `uvm_component_utils(my_agent)

    function new(string name = "", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      drv = my_driver::type_id::create("drv", this);
      sqr = my_sequencer::type_id::create("sqr", this);
    endfunction

    virtual function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      drv.seq_item_port.connect(sqr.seq_item_export);
    endfunction
  endclass

  // Test that runs the sequence
  class seq_test extends uvm_test;
    my_agent agent;
    int pass_count;
    int fail_count;

    `uvm_component_utils(seq_test)

    function new(string name = "seq_test", uvm_component parent = null);
      super.new(name, parent);
      pass_count = 0;
      fail_count = 0;
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      agent = my_agent::type_id::create("agent", this);
    endfunction

    virtual task run_phase(uvm_phase phase);
      my_sequence seq;

      phase.raise_objection(this, "seq_test");
      `uvm_info("TEST", "Starting sequence test", UVM_MEDIUM)

      seq = my_sequence::type_id::create("seq");
      seq.start(agent.sqr);

      `uvm_info("TEST", $sformatf("Sequence done, driver processed %0d items", agent.drv.item_count), UVM_MEDIUM)
      phase.drop_objection(this, "seq_test");
    endtask

    virtual function void report_phase(uvm_phase phase);
      super.report_phase(phase);

      // Check that the expected number of items were processed
      if (agent.drv.item_count == 3) begin
        `uvm_info("TEST", "PASS: Driver processed expected number of items", UVM_NONE)
        pass_count++;
      end else begin
        `uvm_error("TEST", $sformatf("FAIL: Expected 3 items, got %0d", agent.drv.item_count))
        fail_count++;
      end

      `uvm_info("TEST", $sformatf("Test complete: %0d passed, %0d failed", pass_count, fail_count), UVM_NONE)

      if (fail_count == 0) begin
        $write("*-* All Finished *-*\n");
      end
    endfunction
  endclass

  initial begin
    run_test("seq_test");
  end

  initial #10000 $stop;  // timeout
endmodule
