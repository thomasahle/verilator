// DESCRIPTION: Verilator: Test UVM sequence/driver flow with start_item/finish_item
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test sequence/driver communication using start_item/finish_item flow

`include "uvm_macros.svh"

package test_pkg;

  import uvm_pkg::*;

  //----------------------------------------------------------------------
  // Simple transaction class
  //----------------------------------------------------------------------
  class simple_item extends uvm_sequence_item;
    `uvm_object_utils(simple_item)

    rand int unsigned data;
    rand int unsigned addr;
    int item_id;

    function new(string name = "simple_item");
      super.new(name);
    endfunction

    virtual function string convert2string();
      return $sformatf("item_id=%0d addr=0x%0h data=0x%0h", item_id, addr, data);
    endfunction
  endclass

  //----------------------------------------------------------------------
  // Simple sequence that sends items using start_item/finish_item
  //----------------------------------------------------------------------
  class simple_sequence extends uvm_sequence #(simple_item);
    `uvm_object_utils(simple_sequence)

    int num_items = 3;

    function new(string name = "simple_sequence");
      super.new(name);
    endfunction

    virtual task body();
      simple_item item;
      $display("[SEQ] Starting sequence body");
      for (int i = 0; i < num_items; i++) begin
        item = simple_item::type_id::create("item");
        item.item_id = i;
        item.data = 100 + i;
        item.addr = i * 4;
        $display("[SEQ] Starting item %0d @ %0t", i, $time);
        start_item(item);
        $display("[SEQ] Item %0d granted @ %0t", i, $time);
        finish_item(item);
        $display("[SEQ] Item %0d completed @ %0t", i, $time);
      end
      $display("[SEQ] Sequence body complete");
    endtask
  endclass

  //----------------------------------------------------------------------
  // Simple driver that processes items
  //----------------------------------------------------------------------
  class simple_driver extends uvm_driver #(simple_item);
    `uvm_component_utils(simple_driver)

    int items_processed = 0;

    function new(string name = "", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
      simple_item item;
      $display("[DRV] Driver run_phase starting @ %0t", $time);

      forever begin
        // Get next item from sequencer
        seq_item_port.get_next_item(item);
        $display("[DRV] Got item: %s @ %0t", item.convert2string(), $time);

        // Simulate some processing time
        #5;

        // Signal item complete
        seq_item_port.item_done();
        items_processed++;
        $display("[DRV] Item done, processed=%0d @ %0t", items_processed, $time);
      end
    endtask
  endclass

  //----------------------------------------------------------------------
  // Simple agent with sequencer and driver
  //----------------------------------------------------------------------
  class simple_agent extends uvm_agent;
    `uvm_component_utils(simple_agent)

    uvm_sequencer #(simple_item) sequencer;
    simple_driver driver;

    function new(string name = "", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      sequencer = new("sequencer", this);
      driver = simple_driver::type_id::create("driver", this);
      $display("[AGT] Agent build_phase - created sequencer and driver");
    endfunction

    virtual function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      driver.seq_item_port.connect(sequencer);
      $display("[AGT] Agent connect_phase - connected driver to sequencer");
    endfunction
  endclass

  //----------------------------------------------------------------------
  // Test class
  //----------------------------------------------------------------------
  class seq_driver_test extends uvm_test;
    `uvm_component_utils(seq_driver_test)

    simple_agent agent;
    int expected_items = 3;

    function new(string name = "seq_driver_test", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      agent = simple_agent::type_id::create("agent", this);
      $display("[TEST] build_phase - created agent");
    endfunction

    virtual task run_phase(uvm_phase phase);
      simple_sequence seq;
      super.run_phase(phase);
      $display("[TEST] run_phase started @ %0t", $time);
      phase.raise_objection(this, "Running test");

      // Create and start the sequence
      seq = simple_sequence::type_id::create("seq");
      seq.num_items = expected_items;
      $display("[TEST] Starting sequence @ %0t", $time);
      seq.start(agent.sequencer);
      $display("[TEST] Sequence completed @ %0t", $time);

      // Small delay to allow driver to finish
      #10;

      phase.drop_objection(this, "Test complete");
      $display("[TEST] run_phase ended @ %0t", $time);
    endtask

    virtual function void report_phase(uvm_phase phase);
      super.report_phase(phase);
      $display("[TEST] report_phase: driver processed %0d items", agent.driver.items_processed);

      if (agent.driver.items_processed == expected_items) begin
        $display("*-* All Finished *-*");
      end else begin
        $display("%%Error: Expected %0d items processed, got %0d",
                 expected_items, agent.driver.items_processed);
        $stop;
      end
    endfunction
  endclass

endpackage

module t;
  import uvm_pkg::*;
  import test_pkg::*;

  initial begin
    // Register types with factory
    simple_item::type_id::register();
    simple_sequence::type_id::register();
    simple_driver::type_id::register();
    simple_agent::type_id::register();
    seq_driver_test::type_id::register();

    // Run the test
    run_test("seq_driver_test");
  end

endmodule
