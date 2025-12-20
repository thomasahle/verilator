// DESCRIPTION: Verilator: Test for UVM TLM analysis FIFO
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // Simple transaction class
  class my_transaction extends uvm_sequence_item;
    int data;
    int id;

    `uvm_object_utils(my_transaction)

    function new(string name = "my_transaction");
      super.new(name);
    endfunction
  endclass

  // Component with analysis port (producer)
  class producer extends uvm_component;
    uvm_analysis_port #(my_transaction) ap;

    `uvm_component_utils(producer)

    function new(string name = "", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      ap = new("ap", this);
    endfunction

    function void send(int id, int data);
      my_transaction tx = new($sformatf("tx_%0d", id));
      tx.id = id;
      tx.data = data;
      ap.write(tx);
    endfunction
  endclass

  // Component with analysis FIFO (consumer)
  class consumer extends uvm_component;
    uvm_tlm_analysis_fifo #(my_transaction) fifo;
    int received_count;

    `uvm_component_utils(consumer)

    function new(string name = "", uvm_component parent = null);
      super.new(name, parent);
      received_count = 0;
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      fifo = new("fifo", this);
    endfunction

    task get_item();
      my_transaction tx;
      fifo.get(tx);
      `uvm_info("CONSUMER", $sformatf("Got item: id=%0d data=%0d", tx.id, tx.data), UVM_MEDIUM)
      received_count++;
    endtask
  endclass

  // Test that connects producer and consumer
  class analysis_test extends uvm_test;
    producer prod;
    consumer cons;
    int pass_count;
    int fail_count;

    `uvm_component_utils(analysis_test)

    function new(string name = "analysis_test", uvm_component parent = null);
      super.new(name, parent);
      pass_count = 0;
      fail_count = 0;
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      prod = producer::type_id::create("prod", this);
      cons = consumer::type_id::create("cons", this);
    endfunction

    virtual function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      // Connect analysis port to FIFO's analysis export
      prod.ap.connect(cons.fifo.analysis_export);
    endfunction

    virtual task run_phase(uvm_phase phase);
      phase.raise_objection(this, "analysis_test");
      `uvm_info("TEST", "Starting analysis FIFO test", UVM_MEDIUM)

      // Send some transactions
      prod.send(1, 100);
      prod.send(2, 200);
      prod.send(3, 300);

      // Verify FIFO has items
      if (cons.fifo.used() == 3) begin
        `uvm_info("TEST", "PASS: FIFO has expected number of items", UVM_MEDIUM)
        pass_count++;
      end else begin
        `uvm_error("TEST", $sformatf("FAIL: Expected 3 items, got %0d", cons.fifo.used()))
        fail_count++;
      end

      // Get items from FIFO
      cons.get_item();
      cons.get_item();
      cons.get_item();

      // Verify all items were received
      if (cons.received_count == 3) begin
        `uvm_info("TEST", "PASS: Consumer received all items", UVM_MEDIUM)
        pass_count++;
      end else begin
        `uvm_error("TEST", $sformatf("FAIL: Expected 3 items, got %0d", cons.received_count))
        fail_count++;
      end

      // Verify FIFO is empty
      if (cons.fifo.is_empty()) begin
        `uvm_info("TEST", "PASS: FIFO is empty after gets", UVM_MEDIUM)
        pass_count++;
      end else begin
        `uvm_error("TEST", "FAIL: FIFO should be empty")
        fail_count++;
      end

      phase.drop_objection(this, "analysis_test");
    endtask

    virtual function void report_phase(uvm_phase phase);
      super.report_phase(phase);
      `uvm_info("TEST", $sformatf("Test complete: %0d passed, %0d failed", pass_count, fail_count), UVM_NONE)
      if (fail_count == 0)
        $write("*-* All Finished *-*\n");
    endfunction
  endclass

  initial begin
    run_test("analysis_test");
  end

  initial #10000 $stop;  // timeout
endmodule
