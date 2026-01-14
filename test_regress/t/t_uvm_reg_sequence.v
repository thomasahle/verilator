// DESCRIPTION: Verilator: Test UVM register sequence
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test uvm_reg_sequence class

`include "uvm_macros.svh"

module t;
  import uvm_pkg::*;

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

  // Register block
  class my_reg_block extends uvm_reg_block;
    my_reg reg0;
    my_reg reg1;
    uvm_mem data_mem;

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

      data_mem = new("data_mem", 256, 32, "RW", 0);
      data_mem.configure(this, "");

      map = create_map("default_map", 0, 4, UVM_LITTLE_ENDIAN, 1);
      map.add_reg(reg0, 'h0000, "RW", 0, null);
      map.add_reg(reg1, 'h0004, "RW", 0, null);
      map.add_mem(data_mem, 'h1000, "RW", 0, null);

      lock_model();
    endfunction
  endclass

  // Test sequence using uvm_reg_sequence
  class my_reg_seq extends uvm_reg_sequence;
    `uvm_object_utils(my_reg_seq)

    function new(string name = "my_reg_seq");
      super.new(name);
    endfunction

    virtual task body();
      my_reg_block blk;
      uvm_status_e status;
      uvm_reg_data_t value;

      // Cast model to our type
      if (!$cast(blk, model)) begin
        `uvm_error("SEQ", "Failed to cast model")
        return;
      end

      `uvm_info("SEQ", "Starting register sequence", UVM_LOW)

      // Test set/get on registers (basic value operations)
      `uvm_info("SEQ", "Testing set/get", UVM_LOW)
      blk.reg0.set(32'hCAFEBABE);
      value = blk.reg0.get();
      if (value != 32'hCAFEBABE) begin
        `uvm_error("SEQ", $sformatf("set/get mismatch: expected 0xCAFEBABE, got 0x%0h", value))
      end else begin
        `uvm_info("SEQ", "set/get PASSED", UVM_LOW)
      end

      // Test predict and get_mirrored_value
      `uvm_info("SEQ", "Testing predict/get_mirrored_value", UVM_LOW)
      blk.reg1.predict(32'hDEADBEEF, UVM_PREDICT_DIRECT);
      value = blk.reg1.get_mirrored_value();
      if (value != 32'hDEADBEEF) begin
        `uvm_error("SEQ", $sformatf("predict/mirror mismatch: expected 0xDEADBEEF, got 0x%0h", value))
      end else begin
        `uvm_info("SEQ", "predict/get_mirrored_value PASSED", UVM_LOW)
      end

      // Test needs_update
      `uvm_info("SEQ", "Testing needs_update", UVM_LOW)
      blk.reg0.set(32'h12345678);  // Set desired value different from mirrored
      if (!blk.reg0.needs_update()) begin
        `uvm_error("SEQ", "needs_update should return 1")
      end else begin
        `uvm_info("SEQ", "needs_update PASSED", UVM_LOW)
      end

      // Test reset
      `uvm_info("SEQ", "Testing reset", UVM_LOW)
      blk.reg0.reset();
      value = blk.reg0.get();
      if (value != 32'h0) begin  // Reset value is 0
        `uvm_error("SEQ", $sformatf("reset failed: expected 0x0, got 0x%0h", value))
      end else begin
        `uvm_info("SEQ", "reset PASSED", UVM_LOW)
      end

      // Test set_model (already called before body)
      `uvm_info("SEQ", "Testing set_model", UVM_LOW)
      if (model != blk) begin
        `uvm_error("SEQ", "model not set correctly")
      end else if (reg_map != blk.get_default_map()) begin
        `uvm_error("SEQ", "reg_map not set correctly")
      end else begin
        `uvm_info("SEQ", "set_model PASSED", UVM_LOW)
      end

      // Test memory poke/peek
      `uvm_info("SEQ", "Testing memory poke/peek", UVM_LOW)
      blk.data_mem.poke(5, 64'hFEEDFACE);
      value = blk.data_mem.peek(5);
      if (value != 64'hFEEDFACE) begin
        `uvm_error("SEQ", $sformatf("mem poke/peek mismatch: expected 0xFEEDFACE, got 0x%0h", value))
      end else begin
        `uvm_info("SEQ", "memory poke/peek PASSED", UVM_LOW)
      end

      `uvm_info("SEQ", "All sequence operations PASSED", UVM_LOW)
    endtask
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
      my_reg_seq seq;

      phase.raise_objection(this);

      `uvm_info("TEST", "Testing uvm_reg_sequence", UVM_LOW)

      // Create and run the sequence
      seq = new("seq");
      seq.set_model(reg_model);
      seq.body();

      `uvm_info("TEST", "All uvm_reg_sequence tests PASSED", UVM_LOW)

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
