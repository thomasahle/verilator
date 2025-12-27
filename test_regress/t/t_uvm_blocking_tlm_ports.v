// DESCRIPTION: Verilator: Test UVM blocking TLM ports functionality
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test uvm_blocking_put_port, uvm_blocking_get_port

`include "uvm_macros.svh"

module t;
  import uvm_pkg::*;

  // Simple transaction
  class simple_tx extends uvm_object;
    `uvm_object_utils(simple_tx)
    int value;

    function new(string name = "simple_tx");
      super.new(name);
    endfunction
  endclass

  // Producer component with put port
  class producer extends uvm_component;
    `uvm_component_utils(producer)
    uvm_blocking_put_port #(simple_tx) put_port;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      put_port = new("put_port", this);
    endfunction

    task send(int value);
      simple_tx tx = new("tx");
      tx.value = value;
      put_port.put(tx);
    endtask
  endclass

  // Consumer component with put imp
  class consumer extends uvm_component;
    `uvm_component_utils(consumer)
    uvm_blocking_put_imp #(simple_tx, consumer) put_imp;
    simple_tx received_items[$];

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      put_imp = new("put_imp", this);
    endfunction

    virtual task put(simple_tx t);
      received_items.push_back(t);
      `uvm_info("CONSUMER", $sformatf("Received item with value=%0d", t.value), UVM_MEDIUM)
    endtask
  endclass

  // FIFO-like component with get imp
  class fifo_component extends uvm_component;
    `uvm_component_utils(fifo_component)
    uvm_blocking_get_imp #(simple_tx, fifo_component) get_imp;
    simple_tx items[$];

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      get_imp = new("get_imp", this);
    endfunction

    // Pre-populate with items
    function void add_item(int value);
      simple_tx tx = new("tx");
      tx.value = value;
      items.push_back(tx);
    endfunction

    virtual task get(output simple_tx t);
      wait (items.size() > 0);
      t = items.pop_front();
      `uvm_info("FIFO", $sformatf("Providing item with value=%0d", t.value), UVM_MEDIUM)
    endtask
  endclass

  // Getter component with get port
  class getter extends uvm_component;
    `uvm_component_utils(getter)
    uvm_blocking_get_port #(simple_tx) get_port;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      get_port = new("get_port", this);
    endfunction

    task receive(output int value);
      simple_tx tx;
      get_port.get(tx);
      value = tx.value;
    endtask
  endclass

  // Test
  class test extends uvm_test;
    `uvm_component_utils(test)

    producer prod;
    consumer cons;
    fifo_component fifo;
    getter get_comp;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      prod = producer::type_id::create("prod", this);
      cons = consumer::type_id::create("cons", this);
      fifo = fifo_component::type_id::create("fifo", this);
      get_comp = getter::type_id::create("get_comp", this);
    endfunction

    virtual function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      // Connect producer to consumer
      prod.put_port.connect(cons.put_imp);
      // Connect getter to fifo
      get_comp.get_port.connect(fifo.get_imp);
    endfunction

    virtual task run_phase(uvm_phase phase);
      int received_value;

      phase.raise_objection(this);

      // Test put port
      `uvm_info("TEST", "Testing blocking put port", UVM_LOW)
      prod.send(10);
      prod.send(20);
      prod.send(30);

      #10;

      if (cons.received_items.size() != 3) begin
        `uvm_error("TEST", $sformatf("Expected 3 items, got %0d", cons.received_items.size()))
      end
      if (cons.received_items[0].value != 10) begin
        `uvm_error("TEST", $sformatf("Expected value 10, got %0d", cons.received_items[0].value))
      end
      if (cons.received_items[1].value != 20) begin
        `uvm_error("TEST", $sformatf("Expected value 20, got %0d", cons.received_items[1].value))
      end
      if (cons.received_items[2].value != 30) begin
        `uvm_error("TEST", $sformatf("Expected value 30, got %0d", cons.received_items[2].value))
      end
      `uvm_info("TEST", "Put port test PASSED", UVM_LOW)

      // Test get port
      `uvm_info("TEST", "Testing blocking get port", UVM_LOW)
      fifo.add_item(100);
      fifo.add_item(200);
      fifo.add_item(300);

      get_comp.receive(received_value);
      if (received_value != 100) begin
        `uvm_error("TEST", $sformatf("Expected 100, got %0d", received_value))
      end

      get_comp.receive(received_value);
      if (received_value != 200) begin
        `uvm_error("TEST", $sformatf("Expected 200, got %0d", received_value))
      end

      get_comp.receive(received_value);
      if (received_value != 300) begin
        `uvm_error("TEST", $sformatf("Expected 300, got %0d", received_value))
      end
      `uvm_info("TEST", "Get port test PASSED", UVM_LOW)

      `uvm_info("TEST", "All TLM port tests PASSED", UVM_LOW)

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
