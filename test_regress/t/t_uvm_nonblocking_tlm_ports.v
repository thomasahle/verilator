// DESCRIPTION: Verilator: Test UVM nonblocking TLM ports functionality
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test uvm_nonblocking_put_port, uvm_nonblocking_get_port

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

  // Buffer component with nonblocking put imp
  class buffer extends uvm_component;
    `uvm_component_utils(buffer)
    uvm_nonblocking_put_imp #(simple_tx, buffer) put_imp;
    simple_tx items[$];
    int max_size;

    function new(string name, uvm_component parent);
      super.new(name, parent);
      max_size = 3;
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      put_imp = new("put_imp", this);
    endfunction

    virtual function bit try_put(simple_tx t);
      if (items.size() < max_size) begin
        items.push_back(t);
        `uvm_info("BUFFER", $sformatf("Accepted item value=%0d (size=%0d)", t.value, items.size()), UVM_MEDIUM)
        return 1;
      end
      `uvm_info("BUFFER", $sformatf("Rejected item value=%0d (buffer full)", t.value), UVM_MEDIUM)
      return 0;
    endfunction

    virtual function bit can_put();
      return items.size() < max_size;
    endfunction

    function simple_tx get_item();
      if (items.size() > 0)
        return items.pop_front();
      return null;
    endfunction
  endclass

  // Source component with nonblocking get imp
  class source extends uvm_component;
    `uvm_component_utils(source)
    uvm_nonblocking_get_imp #(simple_tx, source) get_imp;
    simple_tx items[$];

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      get_imp = new("get_imp", this);
    endfunction

    function void add_item(int value);
      simple_tx tx = new("tx");
      tx.value = value;
      items.push_back(tx);
    endfunction

    virtual function bit try_get(output simple_tx t);
      if (items.size() > 0) begin
        t = items.pop_front();
        `uvm_info("SOURCE", $sformatf("Providing item value=%0d", t.value), UVM_MEDIUM)
        return 1;
      end
      return 0;
    endfunction

    virtual function bit can_get();
      return items.size() > 0;
    endfunction
  endclass

  // Test
  class test extends uvm_test;
    `uvm_component_utils(test)

    buffer buff;
    source src;
    uvm_nonblocking_put_port #(simple_tx) put_port;
    uvm_nonblocking_get_port #(simple_tx) get_port;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      buff = buffer::type_id::create("buff", this);
      src = source::type_id::create("src", this);
      put_port = new("put_port", this);
      get_port = new("get_port", this);
    endfunction

    virtual function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      put_port.connect(buff.put_imp);
      get_port.connect(src.get_imp);
    endfunction

    virtual task run_phase(uvm_phase phase);
      simple_tx tx;
      bit result;

      phase.raise_objection(this);

      // Test can_put
      `uvm_info("TEST", "Testing can_put", UVM_LOW)
      if (!put_port.can_put()) begin
        `uvm_error("TEST", "can_put should be true when buffer is empty")
      end

      // Test try_put - should succeed 3 times, fail on 4th
      `uvm_info("TEST", "Testing try_put", UVM_LOW)
      tx = new("tx1"); tx.value = 10;
      result = put_port.try_put(tx);
      if (!result) `uvm_error("TEST", "try_put 1 should succeed")

      tx = new("tx2"); tx.value = 20;
      result = put_port.try_put(tx);
      if (!result) `uvm_error("TEST", "try_put 2 should succeed")

      tx = new("tx3"); tx.value = 30;
      result = put_port.try_put(tx);
      if (!result) `uvm_error("TEST", "try_put 3 should succeed")

      // Buffer should be full now
      if (put_port.can_put()) begin
        `uvm_error("TEST", "can_put should be false when buffer is full")
      end

      tx = new("tx4"); tx.value = 40;
      result = put_port.try_put(tx);
      if (result) `uvm_error("TEST", "try_put 4 should fail (buffer full)")

      `uvm_info("TEST", "Put tests PASSED", UVM_LOW)

      // Test can_get
      `uvm_info("TEST", "Testing can_get", UVM_LOW)
      if (get_port.can_get()) begin
        `uvm_error("TEST", "can_get should be false when source is empty")
      end

      // Add items to source
      src.add_item(100);
      src.add_item(200);

      if (!get_port.can_get()) begin
        `uvm_error("TEST", "can_get should be true after adding items")
      end

      // Test try_get
      `uvm_info("TEST", "Testing try_get", UVM_LOW)
      result = get_port.try_get(tx);
      if (!result || tx.value != 100) begin
        `uvm_error("TEST", $sformatf("try_get 1 failed: result=%0d, value=%0d", result, tx.value))
      end

      result = get_port.try_get(tx);
      if (!result || tx.value != 200) begin
        `uvm_error("TEST", $sformatf("try_get 2 failed: result=%0d, value=%0d", result, tx.value))
      end

      // Source should be empty now
      if (get_port.can_get()) begin
        `uvm_error("TEST", "can_get should be false after draining source")
      end

      result = get_port.try_get(tx);
      if (result) begin
        `uvm_error("TEST", "try_get should fail when source is empty")
      end

      `uvm_info("TEST", "Get tests PASSED", UVM_LOW)
      `uvm_info("TEST", "All nonblocking TLM port tests PASSED", UVM_LOW)

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
