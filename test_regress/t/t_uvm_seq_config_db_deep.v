// DESCRIPTION: Verilator: Test uvm_sequence config_db with deep hierarchy
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test config_db lookup from sequences in deep hierarchies (like I3C AVIP pattern)

module t;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // Simple config class
  class env_config extends uvm_object;
    `uvm_object_utils(env_config)
    int value = 42;
    function new(string name = "env_config");
      super.new(name);
    endfunction
  endclass

  // Simple sequence item
  class my_item extends uvm_sequence_item;
    `uvm_object_utils(my_item)
    function new(string name = "my_item");
      super.new(name);
    endfunction
  endclass

  // Virtual base sequence - mimics I3C pattern
  class virtual_base_seq extends uvm_sequence #(my_item);
    `uvm_object_utils(virtual_base_seq)

    env_config cfg_h;

    function new(string name = "virtual_base_seq");
      super.new(name);
    endfunction

    task body();
      string full_name;
      full_name = get_full_name();
      $display("[INFO] Sequence get_full_name() = %s", full_name);

      // Try config_db lookup using the I3C pattern: get(null, get_full_name(), ...)
      if (!uvm_config_db#(env_config)::get(null, get_full_name(), "env_config", cfg_h)) begin
        $display("[FAIL] config_db::get() failed for path: %s", full_name);
        $stop;
      end

      $display("[PASS] config_db::get() succeeded, value = %0d", cfg_h.value);
      if (cfg_h.value != 99) begin
        $display("[FAIL] config value mismatch: expected 99, got %0d", cfg_h.value);
        $stop;
      end
    endtask
  endclass

  // Virtual sequencer - like i3c_virtual_sequencer
  class virtual_sequencer extends uvm_sequencer #(my_item);
    `uvm_component_utils(virtual_sequencer)
    function new(string name = "virtual_sequencer", uvm_component parent = null);
      super.new(name, parent);
    endfunction
  endclass

  // Environment - like i3c_env
  class my_env extends uvm_env;
    `uvm_component_utils(my_env)

    virtual_sequencer virtual_seqr_h;  // Note: created with name "virtual_seqr_h"

    function new(string name = "my_env", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      // Created with name "virtual_seqr_h" (like I3C)
      virtual_seqr_h = virtual_sequencer::type_id::create("virtual_seqr_h", this);
    endfunction
  endclass

  // Test - like i3c_base_test
  class my_test extends uvm_test;
    `uvm_component_utils(my_test)

    my_env env_h;
    env_config cfg_h;

    function new(string name = "my_test", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);

      cfg_h = env_config::type_id::create("cfg_h");
      cfg_h.value = 99;

      env_h = my_env::type_id::create("env_h", this);

      // Set config using wildcard - like I3C: set(this, "*", "env_config", cfg_h)
      uvm_config_db#(env_config)::set(this, "*", "env_config", cfg_h);
      $display("[INFO] Set config at path: %s.*", get_full_name());
    endfunction

    task run_phase(uvm_phase phase);
      virtual_base_seq seq_h;
      phase.raise_objection(this);

      seq_h = virtual_base_seq::type_id::create("my_virtual_seq_h");
      $display("[INFO] Starting sequence on virtual_seqr_h...");
      $display("[INFO] Sequencer path: %s", env_h.virtual_seqr_h.get_full_name());

      seq_h.start(env_h.virtual_seqr_h);

      $display("[PASS] Sequence completed successfully");
      phase.drop_objection(this);
    endtask

    function void report_phase(uvm_phase phase);
      $display("[PASS] Test completed - deep hierarchy config_db works");
      $write("*-* All Coverage Tests Passed *-*\n");
    endfunction
  endclass

  initial begin
    run_test("my_test");
  end

endmodule
