// DESCRIPTION: Verilator: Test UVM register adapter
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test uvm_reg_adapter and uvm_reg_bus_op

`include "uvm_macros.svh"

module t;
  import uvm_pkg::*;

  // Simple transaction class for testing
  class simple_tx extends uvm_sequence_item;
    `uvm_object_utils(simple_tx)

    logic [31:0] addr;
    logic [31:0] data;
    bit is_write;

    function new(string name = "simple_tx");
      super.new(name);
    endfunction

    virtual function string convert2string();
      return $sformatf("addr=0x%08x data=0x%08x is_write=%0d", addr, data, is_write);
    endfunction
  endclass

  // Test adapter implementation
  class test_adapter extends uvm_reg_adapter;
    `uvm_object_utils(test_adapter)

    function new(string name = "test_adapter");
      super.new(name);
      supports_byte_enable = 1;
      provides_responses = 1;
    endfunction

    virtual function uvm_sequence_item reg2bus(const ref uvm_reg_bus_op rw);
      simple_tx tx = simple_tx::type_id::create("tx");
      tx.addr = rw.addr[31:0];
      tx.data = rw.data[31:0];
      tx.is_write = (rw.kind == UVM_WRITE);
      return tx;
    endfunction

    virtual function void bus2reg(uvm_sequence_item bus_item, ref uvm_reg_bus_op rw);
      simple_tx tx;
      if (!$cast(tx, bus_item)) begin
        `uvm_error("TEST_ADAPTER", "Failed to cast bus_item to simple_tx")
        return;
      end
      rw.addr = tx.addr;
      rw.data = tx.data;
      rw.kind = tx.is_write ? UVM_WRITE : UVM_READ;
      rw.status = UVM_IS_OK;
    endfunction
  endclass

  // Test the reg_bus_op struct
  task automatic test_reg_bus_op();
    uvm_reg_bus_op op;

    $display("[%0t] test_reg_bus_op: Starting", $time);

    // Test write operation
    op.kind = UVM_WRITE;
    op.addr = 64'h1000;
    op.data = 64'hDEADBEEF;
    op.n_bits = 32;
    op.status = UVM_IS_OK;
    op.byte_en = 64'hF;

    if (op.kind != UVM_WRITE) begin
      $display("ERROR: Expected UVM_WRITE");
      $stop;
    end
    $display("[%0t] Write op: addr=0x%0h data=0x%0h", $time, op.addr, op.data);

    // Test read operation
    op.kind = UVM_READ;
    op.addr = 64'h2000;

    if (op.kind != UVM_READ) begin
      $display("ERROR: Expected UVM_READ");
      $stop;
    end
    $display("[%0t] Read op: addr=0x%0h", $time, op.addr);

    // Test status values
    op.status = UVM_IS_OK;
    if (op.status != UVM_IS_OK) begin
      $display("ERROR: Expected UVM_IS_OK");
      $stop;
    end

    op.status = UVM_NOT_OK;
    if (op.status != UVM_NOT_OK) begin
      $display("ERROR: Expected UVM_NOT_OK");
      $stop;
    end

    $display("[%0t] test_reg_bus_op: PASSED", $time);
  endtask

  // Test the adapter
  task automatic test_adapter_func();
    test_adapter adapter;
    uvm_reg_bus_op op;
    uvm_sequence_item item;
    simple_tx tx;

    $display("[%0t] test_adapter: Starting", $time);

    adapter = test_adapter::type_id::create("adapter");

    // Check configuration
    if (!adapter.supports_byte_enable) begin
      $display("ERROR: supports_byte_enable should be 1");
      $stop;
    end
    if (!adapter.provides_responses) begin
      $display("ERROR: provides_responses should be 1");
      $stop;
    end
    $display("[%0t] Adapter config: byte_enable=%0d responses=%0d",
             $time, adapter.supports_byte_enable, adapter.provides_responses);

    // Test reg2bus
    op.kind = UVM_WRITE;
    op.addr = 64'h3000;
    op.data = 64'hCAFEBABE;
    op.status = UVM_IS_OK;

    item = adapter.reg2bus(op);
    if (item == null) begin
      $display("ERROR: reg2bus returned null");
      $stop;
    end

    if (!$cast(tx, item)) begin
      $display("ERROR: Failed to cast to simple_tx");
      $stop;
    end

    if (tx.addr != 32'h3000) begin
      $display("ERROR: Wrong addr in tx: 0x%0h", tx.addr);
      $stop;
    end
    if (tx.data != 32'hCAFEBABE) begin
      $display("ERROR: Wrong data in tx: 0x%0h", tx.data);
      $stop;
    end
    if (!tx.is_write) begin
      $display("ERROR: is_write should be 1");
      $stop;
    end
    $display("[%0t] reg2bus: %s", $time, tx.convert2string());

    // Test bus2reg
    tx = new("rx_tx");
    tx.addr = 32'h4000;
    tx.data = 32'h12345678;
    tx.is_write = 0;  // Read

    adapter.bus2reg(tx, op);

    if (op.addr != 64'h4000) begin
      $display("ERROR: Wrong addr from bus2reg: 0x%0h", op.addr);
      $stop;
    end
    if (op.data != 64'h12345678) begin
      $display("ERROR: Wrong data from bus2reg: 0x%0h", op.data);
      $stop;
    end
    if (op.kind != UVM_READ) begin
      $display("ERROR: kind should be UVM_READ");
      $stop;
    end
    if (op.status != UVM_IS_OK) begin
      $display("ERROR: status should be UVM_IS_OK");
      $stop;
    end
    $display("[%0t] bus2reg: addr=0x%0h data=0x%0h kind=%s status=%s",
             $time, op.addr, op.data, op.kind.name(), op.status.name());

    $display("[%0t] test_adapter_func: PASSED", $time);
  endtask

  initial begin
    $display("=== UVM Register Adapter Tests ===");

    test_reg_bus_op();
    #10;

    test_adapter_func();

    $display("\n=== All Tests PASSED ===");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
