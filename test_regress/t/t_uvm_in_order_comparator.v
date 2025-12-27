// DESCRIPTION: Verilator: Test UVM in-order comparator functionality
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test uvm_in_order_comparator

`include "uvm_macros.svh"

module t;
  import uvm_pkg::*;

  // Simple transaction for testing
  class my_transaction extends uvm_object;
    `uvm_object_utils(my_transaction)
    rand int value;
    rand bit [7:0] data;

    function new(string name = "my_transaction");
      super.new(name);
    endfunction

    virtual function bit compare(uvm_object rhs, uvm_comparer comparer = null);
      my_transaction rhs_tx;
      if (!$cast(rhs_tx, rhs)) return 0;
      return (this.value == rhs_tx.value && this.data == rhs_tx.data);
    endfunction
  endclass

  // Producer component
  class producer extends uvm_component;
    `uvm_component_utils(producer)
    uvm_analysis_port #(my_transaction) ap;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      ap = new("ap", this);
    endfunction

    function void send(int value, bit [7:0] data);
      my_transaction tx = new("tx");
      tx.value = value;
      tx.data = data;
      ap.write(tx);
    endfunction
  endclass

  // Test
  class test extends uvm_test;
    `uvm_component_utils(test)

    producer expected_prod;
    producer actual_prod;
    uvm_in_order_comparator #(my_transaction) comparator;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      expected_prod = producer::type_id::create("expected_prod", this);
      actual_prod = producer::type_id::create("actual_prod", this);
      comparator = new("comparator", this);
    endfunction

    virtual function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      // Connect expected producer to before_export
      expected_prod.ap.connect(comparator.m_before_fifo.analysis_export);
      // Connect actual producer to after_export
      actual_prod.ap.connect(comparator.m_after_fifo.analysis_export);
    endfunction

    virtual task run_phase(uvm_phase phase);
      phase.raise_objection(this);

      `uvm_info("TEST", "Testing matching transactions", UVM_LOW)

      // Send matching transactions
      expected_prod.send(10, 8'hAA);
      actual_prod.send(10, 8'hAA);
      comparator.do_compare();

      expected_prod.send(20, 8'hBB);
      actual_prod.send(20, 8'hBB);
      comparator.do_compare();

      expected_prod.send(30, 8'hCC);
      actual_prod.send(30, 8'hCC);
      comparator.do_compare();

      `uvm_info("TEST", $sformatf("After matching: Matches=%0d, Mismatches=%0d",
                comparator.get_matches(), comparator.get_mismatches()), UVM_LOW)

      if (comparator.get_matches() != 3) begin
        `uvm_error("TEST", $sformatf("Expected 3 matches, got %0d", comparator.get_matches()))
      end
      if (comparator.get_mismatches() != 0) begin
        `uvm_error("TEST", $sformatf("Expected 0 mismatches, got %0d", comparator.get_mismatches()))
      end

      // Test mismatching transactions
      `uvm_info("TEST", "Testing mismatching transactions", UVM_LOW)

      expected_prod.send(100, 8'hDD);
      actual_prod.send(100, 8'hEE);  // Different data
      comparator.do_compare();

      expected_prod.send(200, 8'hFF);
      actual_prod.send(201, 8'hFF);  // Different value
      comparator.do_compare();

      `uvm_info("TEST", $sformatf("After mismatching: Matches=%0d, Mismatches=%0d",
                comparator.get_matches(), comparator.get_mismatches()), UVM_LOW)

      if (comparator.get_matches() != 3) begin
        `uvm_error("TEST", $sformatf("Expected 3 matches, got %0d", comparator.get_matches()))
      end
      if (comparator.get_mismatches() != 2) begin
        `uvm_error("TEST", $sformatf("Expected 2 mismatches, got %0d", comparator.get_mismatches()))
      end

      // Test flush
      comparator.flush();
      if (!comparator.m_before_fifo.is_empty() || !comparator.m_after_fifo.is_empty()) begin
        `uvm_error("TEST", "Flush failed - FIFOs not empty")
      end

      `uvm_info("TEST", "All comparator tests PASSED", UVM_LOW)

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
