// DESCRIPTION: Verilator: Test uvm_sequence get_full_name() for config_db lookups
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test that sequences properly return hierarchical path in get_full_name()
// which is required for uvm_config_db lookups to work correctly

module t;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // Simple config class
  class my_config extends uvm_object;
    `uvm_object_utils(my_config)
    int value = 42;
    function new(string name = "my_config");
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

  // Sequence that uses config_db
  class my_sequence extends uvm_sequence #(my_item);
    `uvm_object_utils(my_sequence)

    my_config cfg;

    function new(string name = "my_sequence");
      super.new(name);
    endfunction

    task body();
      string full_name;
      full_name = get_full_name();
      $display("[PASS] Sequence get_full_name() = %s", full_name);

      // Verify path includes sequencer hierarchy
      if (full_name == "my_sequence") begin
        $display("[FAIL] get_full_name() should include sequencer path, got: %s", full_name);
        $stop;
      end

      // Try config_db lookup using get_full_name()
      if (!uvm_config_db#(my_config)::get(null, get_full_name(), "cfg", cfg)) begin
        $display("[FAIL] config_db::get() failed for path: %s", full_name);
        $stop;
      end

      $display("[PASS] config_db::get() succeeded, value = %0d", cfg.value);
      if (cfg.value != 42) begin
        $display("[FAIL] config value mismatch");
        $stop;
      end
    endtask
  endclass

  // Simple sequencer
  class my_sequencer extends uvm_sequencer #(my_item);
    `uvm_component_utils(my_sequencer)
    function new(string name = "my_sequencer", uvm_component parent = null);
      super.new(name, parent);
    endfunction
  endclass

  // Test component
  class my_test extends uvm_test;
    `uvm_component_utils(my_test)

    my_sequencer sqr;
    my_config cfg;

    function new(string name = "my_test", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      sqr = my_sequencer::type_id::create("sqr", this);
      cfg = my_config::type_id::create("cfg");
      cfg.value = 42;
      // Set config using wildcard - should be accessible from sequence running on sqr
      uvm_config_db#(my_config)::set(this, "*", "cfg", cfg);
    endfunction

    task run_phase(uvm_phase phase);
      my_sequence seq;
      phase.raise_objection(this);

      seq = my_sequence::type_id::create("seq");
      $display("[INFO] Starting sequence on sequencer...");
      seq.start(sqr);

      $display("[PASS] Sequence completed successfully");
      phase.drop_objection(this);
    endtask

    function void report_phase(uvm_phase phase);
      $display("[PASS] Test completed - sequence get_full_name() works for config_db");
      $write("*-* All Coverage Tests Passed *-*\n");
    endfunction
  endclass

  initial begin
    run_test("my_test");
  end

endmodule
