// DESCRIPTION: Verilator: Test UVM register predictor and sequence
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test uvm_reg_predictor, uvm_reg_sequence, uvm_reg_item

`include "uvm_macros.svh"

module t;
  import uvm_pkg::*;

  // Simple bus transaction
  class bus_tx extends uvm_sequence_item;
    `uvm_object_utils(bus_tx)
    logic [31:0] addr;
    logic [31:0] data;
    bit write;

    function new(string name = "bus_tx");
      super.new(name);
    endfunction
  endclass

  // Simple adapter
  class my_adapter extends uvm_reg_adapter;
    function new(string name = "my_adapter");
      super.new(name);
    endfunction

    virtual function uvm_sequence_item reg2bus(const ref uvm_reg_bus_op rw);
      bus_tx tx = new("tx");
      tx.addr = rw.addr[31:0];
      tx.data = rw.data[31:0];
      tx.write = (rw.kind == UVM_WRITE);
      return tx;
    endfunction

    virtual function void bus2reg(uvm_sequence_item bus_item, ref uvm_reg_bus_op rw);
      bus_tx tx;
      if ($cast(tx, bus_item)) begin
        rw.addr = tx.addr;
        rw.data = tx.data;
        rw.kind = tx.write ? UVM_WRITE : UVM_READ;
        rw.status = UVM_IS_OK;
      end
    endfunction
  endclass

  // Simple register
  class my_reg extends uvm_reg;
    uvm_reg_field value;

    function new(string name = "my_reg");
      super.new(name, 32, 0);
    endfunction

    virtual function void build();
      value = new("value");
      value.configure(this, 32, 0, "RW", 0, 32'h0, 1, 1, 1);
      add_field(value);
    endfunction
  endclass

  // Simple reg block
  class my_reg_block extends uvm_reg_block;
    my_reg reg0;
    my_reg reg1;

    function new(string name = "my_reg_block");
      super.new(name, 0);
    endfunction

    virtual function void build();
      uvm_reg_map map;

      reg0 = new("reg0");
      reg0.build();
      reg0.configure(this, null, "");

      reg1 = new("reg1");
      reg1.build();
      reg1.configure(this, null, "");

      map = create_map("default_map", 0, 4, UVM_LITTLE_ENDIAN, 1);
      map.add_reg(reg0, 'h0000, "RW", 0, null);
      map.add_reg(reg1, 'h0004, "RW", 0, null);

      lock_model();
    endfunction
  endclass

  // Test
  class test extends uvm_test;
    `uvm_component_utils(test)

    my_reg_block reg_model;
    my_adapter adapter;
    uvm_reg_predictor #(bus_tx) predictor;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      reg_model = new("reg_model");
      reg_model.build();
      adapter = new("adapter");
      predictor = new("predictor", this);
    endfunction

    virtual function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      predictor.set_map(reg_model.get_default_map());
      predictor.set_adapter(adapter);
    endfunction

    virtual task run_phase(uvm_phase phase);
      bus_tx tx;

      phase.raise_objection(this);

      `uvm_info("TEST", "Testing uvm_reg_predictor", UVM_LOW)

      // Test predictor by sending bus transactions
      tx = new("tx");
      tx.addr = 32'h0000;
      tx.data = 32'hDEADBEEF;
      tx.write = 1;

      // Write to reg0 via predictor
      predictor.write(tx);

      // Check that reg0 was updated
      if (reg_model.reg0.get_mirrored_value() != 32'hDEADBEEF) begin
        `uvm_error("TEST", $sformatf("Predictor failed: expected 0xDEADBEEF, got 0x%0h",
                  reg_model.reg0.get_mirrored_value()))
      end else begin
        `uvm_info("TEST", "Predictor write prediction PASSED", UVM_LOW)
      end

      // Read from reg1 via predictor
      tx = new("tx");
      tx.addr = 32'h0004;
      tx.data = 32'h12345678;
      tx.write = 0;
      predictor.write(tx);

      if (reg_model.reg1.get_mirrored_value() != 32'h12345678) begin
        `uvm_error("TEST", $sformatf("Predictor read failed: expected 0x12345678, got 0x%0h",
                  reg_model.reg1.get_mirrored_value()))
      end else begin
        `uvm_info("TEST", "Predictor read prediction PASSED", UVM_LOW)
      end

      // Test uvm_reg_item
      `uvm_info("TEST", "Testing uvm_reg_item", UVM_LOW)
      begin
        uvm_reg_item item = new("item");
        item.rw.addr = 64'h100;
        item.rw.data = 64'hCAFE;
        item.rw.kind = UVM_WRITE;
        if (item.rw.addr != 64'h100 || item.rw.data != 64'hCAFE) begin
          `uvm_error("TEST", "uvm_reg_item failed")
        end else begin
          `uvm_info("TEST", "uvm_reg_item PASSED", UVM_LOW)
        end
      end

      // Test uvm_check_e enum
      `uvm_info("TEST", "Testing uvm_check_e", UVM_LOW)
      begin
        uvm_check_e check;
        check = UVM_NO_CHECK;
        if (check != 0) `uvm_error("TEST", "UVM_NO_CHECK wrong value")
        check = UVM_DO_CHECK;
        if (check != 1) `uvm_error("TEST", "UVM_DO_CHECK wrong value")
        `uvm_info("TEST", "uvm_check_e PASSED", UVM_LOW)
      end

      `uvm_info("TEST", "All predictor tests PASSED", UVM_LOW)

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
