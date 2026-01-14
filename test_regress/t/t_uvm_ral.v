// DESCRIPTION: Verilator: Test UVM Register Abstraction Layer
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test uvm_reg, uvm_reg_field, uvm_reg_block, uvm_reg_map, uvm_mem

`include "uvm_macros.svh"

module t;
  import uvm_pkg::*;

  // Example register with fields
  class my_reg extends uvm_reg;
    uvm_reg_field data;
    uvm_reg_field enable;
    uvm_reg_field mode;

    function new(string name = "my_reg");
      super.new(name, 32, 0);
    endfunction

    virtual function void build();
      data = new("data");
      data.configure(this, 16, 0, "RW", 0, 16'hABCD, 1, 1, 1);
      add_field(data);

      enable = new("enable");
      enable.configure(this, 1, 16, "RW", 0, 1'b0, 1, 1, 1);
      add_field(enable);

      mode = new("mode");
      mode.configure(this, 3, 17, "RW", 0, 3'b010, 1, 1, 1);
      add_field(mode);
    endfunction
  endclass

  // Example register block
  class my_reg_block extends uvm_reg_block;
    my_reg ctrl_reg;
    my_reg status_reg;
    uvm_mem data_mem;

    function new(string name = "my_reg_block");
      super.new(name, 0);
    endfunction

    virtual function void build();
      uvm_reg_map map;

      // Create and configure registers
      ctrl_reg = new("ctrl_reg");
      ctrl_reg.build();
      ctrl_reg.configure(this, null, "");

      status_reg = new("status_reg");
      status_reg.build();
      status_reg.configure(this, null, "");

      // Create memory
      data_mem = new("data_mem", 256, 32, "RW", 0);
      data_mem.configure(this, "");

      // Create address map
      map = create_map("default_map", 0, 4, UVM_LITTLE_ENDIAN, 1);
      map.add_reg(ctrl_reg, 'h0000, "RW", 0, null);
      map.add_reg(status_reg, 'h0004, "RW", 0, null);
      map.add_mem(data_mem, 'h1000, "RW", 0, null);

      lock_model();
    endfunction
  endclass

  // Test
  class test extends uvm_test;
    `uvm_component_utils(test)

    my_reg_block reg_model;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      reg_model = new("reg_model");
      reg_model.build();
    endfunction

    virtual task run_phase(uvm_phase phase);
      uvm_reg_data_t value;
      uvm_status_e status;
      uvm_reg regs[$];
      uvm_mem mems[$];
      uvm_reg_map maps[$];

      phase.raise_objection(this);

      `uvm_info("TEST", "Testing RAL classes", UVM_LOW)

      // Test register field access
      `uvm_info("TEST", "Testing register fields", UVM_LOW)
      `uvm_info("TEST", $sformatf("data field bits: %0d", reg_model.ctrl_reg.data.get_n_bits()), UVM_LOW)
      `uvm_info("TEST", $sformatf("data field lsb: %0d", reg_model.ctrl_reg.data.get_lsb_pos()), UVM_LOW)

      // Test set/get
      reg_model.ctrl_reg.data.set(16'h1234);
      if (reg_model.ctrl_reg.data.get() != 16'h1234) begin
        `uvm_error("TEST", $sformatf("data.get() failed: expected 0x1234, got 0x%0h", reg_model.ctrl_reg.data.get()))
      end

      // Test composite register get
      reg_model.ctrl_reg.enable.set(1);
      reg_model.ctrl_reg.mode.set(3'b101);
      value = reg_model.ctrl_reg.get();
      `uvm_info("TEST", $sformatf("Composite register value: 0x%0h", value), UVM_LOW)

      // Test reset
      reg_model.ctrl_reg.reset();
      if (reg_model.ctrl_reg.data.get() != 16'hABCD) begin
        `uvm_error("TEST", $sformatf("Reset failed: expected 0xABCD, got 0x%0h", reg_model.ctrl_reg.data.get()))
      end

      // Test block methods
      `uvm_info("TEST", "Testing register block", UVM_LOW)
      reg_model.get_registers(regs, UVM_HIER);
      `uvm_info("TEST", $sformatf("Number of registers: %0d", regs.size()), UVM_LOW)
      if (regs.size() != 2) begin
        `uvm_error("TEST", $sformatf("Expected 2 registers, got %0d", regs.size()))
      end

      reg_model.get_memories(mems, UVM_HIER);
      `uvm_info("TEST", $sformatf("Number of memories: %0d", mems.size()), UVM_LOW)
      if (mems.size() != 1) begin
        `uvm_error("TEST", $sformatf("Expected 1 memory, got %0d", mems.size()))
      end

      reg_model.get_maps(maps);
      `uvm_info("TEST", $sformatf("Number of maps: %0d", maps.size()), UVM_LOW)
      if (maps.size() != 1) begin
        `uvm_error("TEST", $sformatf("Expected 1 map, got %0d", maps.size()))
      end

      // Test get_by_name
      if (reg_model.get_reg_by_name("ctrl_reg") != reg_model.ctrl_reg) begin
        `uvm_error("TEST", "get_reg_by_name failed")
      end

      if (reg_model.get_mem_by_name("data_mem") != reg_model.data_mem) begin
        `uvm_error("TEST", "get_mem_by_name failed")
      end

      // Test memory access
      `uvm_info("TEST", "Testing memory", UVM_LOW)
      reg_model.data_mem.poke(0, 64'hDEADBEEF);
      if (reg_model.data_mem.peek(0) != 64'hDEADBEEF) begin
        `uvm_error("TEST", "Memory poke/peek failed")
      end

      reg_model.data_mem.write(status, 10, 64'h12345678);
      reg_model.data_mem.read(status, 10, value);
      if (value != 64'h12345678) begin
        `uvm_error("TEST", $sformatf("Memory read/write failed: got 0x%0h", value))
      end

      // Test map methods
      `uvm_info("TEST", "Testing register map", UVM_LOW)
      if (reg_model.get_default_map().get_reg_by_offset(0) != reg_model.ctrl_reg) begin
        `uvm_error("TEST", "get_reg_by_offset failed")
      end

      if (reg_model.get_default_map().get_mem_by_offset('h1000) != reg_model.data_mem) begin
        `uvm_error("TEST", "get_mem_by_offset failed")
      end

      `uvm_info("TEST", "All RAL tests PASSED", UVM_LOW)

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
