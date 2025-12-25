// DESCRIPTION: Verilator: Test UVM sequence mechanism
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Import UVM package for base classes
import uvm_pkg::*;
`include "uvm_macros.svh"

// Simple transaction class
class simple_tx extends uvm_sequence_item;
   rand bit [31:0] data;
   rand bit [15:0] addr;

   `uvm_object_utils_begin(simple_tx)
      `uvm_field_int(data, UVM_ALL_ON)
      `uvm_field_int(addr, UVM_ALL_ON)
   `uvm_object_utils_end

   function new(string name = "simple_tx");
      super.new(name);
   endfunction
endclass

// Simple driver
class simple_driver extends uvm_driver #(simple_tx);
   `uvm_component_utils(simple_driver)

   int items_driven = 0;

   function new(string name, uvm_component parent);
      super.new(name, parent);
   endfunction

   task run_phase(uvm_phase phase);
      simple_tx tx;
      forever begin
         seq_item_port.get_next_item(tx);
         `uvm_info("DRV", $sformatf("Driving tx: addr=%h data=%h", tx.addr, tx.data), UVM_LOW)
         items_driven++;
         // No delay - process immediately like t_uvm_full_sim
         seq_item_port.item_done();
      end
   endtask
endclass

// Simple sequencer
class simple_sequencer extends uvm_sequencer #(simple_tx);
   `uvm_component_utils(simple_sequencer)

   function new(string name, uvm_component parent);
      super.new(name, parent);
   endfunction
endclass

// Simple sequence
class simple_seq extends uvm_sequence #(simple_tx);
   `uvm_object_utils(simple_seq)

   rand int num_items;
   constraint num_c { num_items inside {[3:5]}; }

   function new(string name = "simple_seq");
      super.new(name);
   endfunction

   task body();
      simple_tx tx;
      `uvm_info("SEQ", $sformatf("Starting sequence with %0d items", num_items), UVM_LOW)

      for (int i = 0; i < num_items; i++) begin
         tx = new($sformatf("tx_%0d", i));
         start_item(tx);
         if (!tx.randomize()) begin
            `uvm_error("SEQ", "Randomization failed")
         end
         `uvm_info("SEQ", $sformatf("Sending tx[%0d]: addr=%h data=%h", i, tx.addr, tx.data), UVM_LOW)
         finish_item(tx);
      end

      `uvm_info("SEQ", "Sequence complete", UVM_LOW)
   endtask
endclass

// Simple agent
class simple_agent extends uvm_agent;
   `uvm_component_utils(simple_agent)

   simple_driver drv;
   simple_sequencer seqr;

   function new(string name, uvm_component parent);
      super.new(name, parent);
   endfunction

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      drv = simple_driver::type_id::create("drv", this);
      seqr = simple_sequencer::type_id::create("seqr", this);
   endfunction

   function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      drv.seq_item_port.connect(seqr.seq_item_export);
   endfunction
endclass

// Test class
class simple_test extends uvm_test;
   `uvm_component_utils(simple_test)

   simple_agent agent;

   function new(string name, uvm_component parent);
      super.new(name, parent);
   endfunction

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      agent = simple_agent::type_id::create("agent", this);
   endfunction

   task run_phase(uvm_phase phase);
      simple_seq seq;

      phase.raise_objection(this);

      `uvm_info("TEST", "Starting test", UVM_LOW)

      seq = new("seq");
      if (!seq.randomize() with { num_items == 3; }) begin
         `uvm_error("TEST", "Sequence randomize failed")
      end

      `uvm_info("TEST", "Running sequence on sequencer", UVM_LOW)
      seq.start(agent.seqr);
      `uvm_info("TEST", "Sequence finished", UVM_LOW)

      if (agent.drv.items_driven == 3) begin
         `uvm_info("TEST", $sformatf("PASS: Driver received %0d items as expected", agent.drv.items_driven), UVM_LOW)
      end else begin
         `uvm_error("TEST", $sformatf("FAIL: Expected 3 items, got %0d", agent.drv.items_driven))
      end

      phase.drop_objection(this);
   endtask

   function void report_phase(uvm_phase phase);
      super.report_phase(phase);
      if (agent.drv.items_driven == 3) begin
         $display("*-* All Finished *-*");
      end
   endfunction
endclass

module t;
   import uvm_pkg::*;

   initial begin
      run_test("simple_test");
   end
endmodule
