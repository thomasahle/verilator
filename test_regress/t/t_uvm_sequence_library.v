// DESCRIPTION: Verilator: Test UVM sequence library functionality
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test uvm_sequence_library

`include "uvm_macros.svh"

module t;
  import uvm_pkg::*;

  // Simple transaction
  class simple_tx extends uvm_sequence_item;
    `uvm_object_utils(simple_tx)
    int data;
    function new(string name = "simple_tx");
      super.new(name);
    endfunction
  endclass

  // Sequence A
  class seq_a extends uvm_sequence #(simple_tx);
    `uvm_object_utils(seq_a)
    static int exec_count = 0;

    function new(string name = "seq_a");
      super.new(name);
    endfunction

    virtual task body();
      `uvm_info("SEQ_A", "Executing sequence A", UVM_MEDIUM)
      exec_count++;
    endtask
  endclass

  // Sequence B
  class seq_b extends uvm_sequence #(simple_tx);
    `uvm_object_utils(seq_b)
    static int exec_count = 0;

    function new(string name = "seq_b");
      super.new(name);
    endfunction

    virtual task body();
      `uvm_info("SEQ_B", "Executing sequence B", UVM_MEDIUM)
      exec_count++;
    endtask
  endclass

  // Sequence C
  class seq_c extends uvm_sequence #(simple_tx);
    `uvm_object_utils(seq_c)
    static int exec_count = 0;

    function new(string name = "seq_c");
      super.new(name);
    endfunction

    virtual task body();
      `uvm_info("SEQ_C", "Executing sequence C", UVM_MEDIUM)
      exec_count++;
    endtask
  endclass

  // Simple driver
  class simple_driver extends uvm_driver #(simple_tx);
    `uvm_component_utils(simple_driver)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
      // Minimal driver - just accept items
      forever begin
        simple_tx tx;
        seq_item_port.get_next_item(tx);
        seq_item_port.item_done();
      end
    endtask
  endclass

  // Test
  class test extends uvm_test;
    `uvm_component_utils(test)

    uvm_sequencer #(simple_tx) seqr;
    simple_driver drv;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      seqr = new("seqr", this);
      drv = simple_driver::type_id::create("drv", this);
    endfunction

    virtual function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      drv.seq_item_port.connect(seqr.seq_item_export);
    endfunction

    virtual task run_phase(uvm_phase phase);
      uvm_sequence_library #(simple_tx) seq_lib;
      seq_a a;
      seq_b b;
      seq_c c;

      phase.raise_objection(this);

      // Create sequences
      a = seq_a::type_id::create("a");
      b = seq_b::type_id::create("b");
      c = seq_c::type_id::create("c");

      // Create sequence library
      seq_lib = new("seq_lib");

      // Test get_num_sequences when empty
      if (seq_lib.get_num_sequences() != 0) begin
        `uvm_error("TEST", $sformatf("Expected 0 sequences, got %0d", seq_lib.get_num_sequences()))
      end

      // Add sequences
      seq_lib.add_sequence(a);
      seq_lib.add_sequence(b);
      seq_lib.add_sequence(c);

      // Test get_num_sequences
      if (seq_lib.get_num_sequences() != 3) begin
        `uvm_error("TEST", $sformatf("Expected 3 sequences, got %0d", seq_lib.get_num_sequences()))
      end

      // Set count and mode
      seq_lib.set_random_count(5, 5);  // Exactly 5 executions
      seq_lib.set_selection_mode(UVM_SEQ_LIB_RANDC);

      // Start the library
      `uvm_info("TEST", "Starting sequence library", UVM_LOW)
      seq_lib.start(seqr);

      #100;

      // Check that sequences were executed
      `uvm_info("TEST", $sformatf("seq_a executed %0d times", seq_a::exec_count), UVM_LOW)
      `uvm_info("TEST", $sformatf("seq_b executed %0d times", seq_b::exec_count), UVM_LOW)
      `uvm_info("TEST", $sformatf("seq_c executed %0d times", seq_c::exec_count), UVM_LOW)

      if (seq_a::exec_count + seq_b::exec_count + seq_c::exec_count != 5) begin
        `uvm_error("TEST", "Total execution count should be 5")
      end else begin
        `uvm_info("TEST", "PASS: Sequence library executed correctly", UVM_LOW)
      end

      phase.drop_objection(this);
    endtask

    virtual function void report_phase(uvm_phase phase);
      super.report_phase(phase);
      $write("*-* All Finished *-*\n");
    endfunction
  endclass

  initial begin
    run_test("test");
  end
endmodule
