// DESCRIPTION: Verilator: Test for UVM analysis port with coverage subscriber
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test analysis port write with coverage subscriber
// Reproduces SPI AVIP issue where transaction is null at coverage sample

module t;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // Simple transaction class
  class MyTransaction extends uvm_sequence_item;
    `uvm_object_utils(MyTransaction)

    rand bit [7:0] data;
    rand bit [3:0] addr;

    function new(string name = "MyTransaction");
      super.new(name);
    endfunction

    virtual function string convert2string();
      return $sformatf("data=%0h addr=%0h", data, addr);
    endfunction
  endclass

  // Coverage subscriber
  class MyCoverage extends uvm_subscriber #(MyTransaction);
    `uvm_component_utils(MyCoverage)

    covergroup my_cg with function sample(MyTransaction pkt);
      option.per_instance = 1;
      DATA_CP: coverpoint pkt.data {
        bins low = {[0:127]};
        bins high = {[128:255]};
      }
      ADDR_CP: coverpoint pkt.addr {
        bins b[] = {[0:15]};
      }
    endgroup

    function new(string name = "MyCoverage", uvm_component parent = null);
      super.new(name, parent);
      my_cg = new();
    endfunction

    virtual function void write(MyTransaction t);
      $display("[%0t] MyCoverage::write called, t=%p", $time, t);
      if (t == null) begin
        $display("[%0t] ERROR: Transaction is NULL!", $time);
        $stop;
      end
      $display("[%0t] Transaction: %s", $time, t.convert2string());
      my_cg.sample(t);
      $display("[%0t] Coverage sampled successfully", $time);
    endfunction

    virtual function void report_phase(uvm_phase phase);
      $display("Coverage = %0.2f%%", my_cg.get_coverage());
    endfunction
  endclass

  // Monitor that writes transactions
  class MyMonitor extends uvm_component;
    `uvm_component_utils(MyMonitor)

    uvm_analysis_port #(MyTransaction) ap;

    function new(string name = "MyMonitor", uvm_component parent = null);
      super.new(name, parent);
      ap = new("ap", this);
    endfunction

    task run_phase(uvm_phase phase);
      MyTransaction txn;
      MyTransaction clone_txn;

      phase.raise_objection(this);

      // Create and send a transaction - test that clone works
      txn = MyTransaction::type_id::create("txn");
      void'(txn.randomize());
      $display("[%0t] Monitor: Created txn: %s", $time, txn.convert2string());

      // Clone and send (like SPI AVIP does)
      $cast(clone_txn, txn.clone());
      $display("[%0t] Monitor: Cloned txn, clone_txn=%p", $time, clone_txn);
      if (clone_txn == null) begin
        $display("[%0t] ERROR: Clone returned NULL!", $time);
        $stop;
      end

      ap.write(clone_txn);
      $display("[%0t] Monitor: Wrote to analysis port", $time);
      $display("*-* All Finished *-*");
      $finish;
    endtask
  endclass

  // Test that connects monitor to coverage
  class MyTest extends uvm_test;
    `uvm_component_utils(MyTest)

    MyMonitor mon;
    MyCoverage cov;

    function new(string name = "MyTest", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      mon = MyMonitor::type_id::create("mon", this);
      cov = MyCoverage::type_id::create("cov", this);
    endfunction

    function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      mon.ap.connect(cov.analysis_export);
    endfunction
  endclass

  initial begin
    run_test("MyTest");
  end

endmodule
