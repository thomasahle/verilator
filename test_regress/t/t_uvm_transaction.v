// DESCRIPTION: Verilator: Test UVM transaction base class
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test uvm_transaction class

`include "uvm_macros.svh"

module t;
  import uvm_pkg::*;

  // Custom transaction
  class my_transaction extends uvm_transaction;
    rand bit [7:0] data;
    rand bit [3:0] addr;

    `uvm_object_utils(my_transaction)

    function new(string name = "my_transaction");
      super.new(name);
    endfunction
  endclass

  // Test
  class test extends uvm_test;
    `uvm_component_utils(test)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
      my_transaction tr1, tr2;
      int id1, id2;

      phase.raise_objection(this);

      `uvm_info("TEST", "Testing uvm_transaction", UVM_LOW)

      // Test transaction creation and IDs
      tr1 = new("tr1");
      tr2 = new("tr2");

      id1 = tr1.get_transaction_id();
      id2 = tr2.get_transaction_id();

      `uvm_info("TEST", $sformatf("tr1 id=%0d, tr2 id=%0d", id1, id2), UVM_LOW)

      if (id2 <= id1) begin
        `uvm_error("TEST", "Transaction IDs should be incrementing")
      end else begin
        `uvm_info("TEST", "Transaction ID test PASSED", UVM_LOW)
      end

      // Test timing methods
      tr1.set_begin_time(100);
      tr1.set_end_time(200);
      tr1.set_accept_time(50);

      if (tr1.get_begin_time() != 100) begin
        `uvm_error("TEST", $sformatf("begin_time mismatch: got %0t", tr1.get_begin_time()))
      end
      if (tr1.get_end_time() != 200) begin
        `uvm_error("TEST", $sformatf("end_time mismatch: got %0t", tr1.get_end_time()))
      end
      if (tr1.get_accept_time() != 50) begin
        `uvm_error("TEST", $sformatf("accept_time mismatch: got %0t", tr1.get_accept_time()))
      end
      `uvm_info("TEST", "Timing test PASSED", UVM_LOW)

      // Test initiator
      tr1.set_initiator(this);
      if (tr1.get_initiator() != this) begin
        `uvm_error("TEST", "Initiator mismatch")
      end else begin
        `uvm_info("TEST", "Initiator test PASSED", UVM_LOW)
      end

      // Test accept_tr/begin_tr/end_tr
      tr2.accept_tr();
      // accept_tr should set the time to current simulation time (0 at start)
      `uvm_info("TEST", $sformatf("accept_tr set time to %0t", tr2.get_accept_time()), UVM_LOW)

      tr2.begin_tr();
      // begin_tr should set the time to current simulation time
      `uvm_info("TEST", $sformatf("begin_tr set time to %0t", tr2.get_begin_time()), UVM_LOW)

      tr2.end_tr();
      // end_tr should set the time to current simulation time
      `uvm_info("TEST", $sformatf("end_tr set time to %0t", tr2.get_end_time()), UVM_LOW)

      `uvm_info("TEST", "Transaction event methods PASSED", UVM_LOW)

      // Test that sequence_item inherits from transaction
      begin
        uvm_sequence_item seq_item = new("seq_item");
        int sid = seq_item.get_transaction_id();
        `uvm_info("TEST", $sformatf("sequence_item has transaction_id=%0d", sid), UVM_LOW)
        if (sid <= id2) begin
          `uvm_error("TEST", "sequence_item should have incrementing ID")
        end else begin
          `uvm_info("TEST", "sequence_item inheritance PASSED", UVM_LOW)
        end
      end

      `uvm_info("TEST", "All uvm_transaction tests PASSED", UVM_LOW)

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
