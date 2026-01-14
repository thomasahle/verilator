// DESCRIPTION: Verilator: Test UVM TLM (analysis ports and fifos)
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test TLM communication: analysis ports, analysis imps, and TLM fifos

`include "uvm_macros.svh"

package test_pkg;

  import uvm_pkg::*;

  //----------------------------------------------------------------------
  // Simple transaction class
  //----------------------------------------------------------------------
  class simple_txn extends uvm_object;
    `uvm_object_utils(simple_txn)

    int value;
    int id;

    function new(string name = "simple_txn");
      super.new(name);
    endfunction

    virtual function string convert2string();
      return $sformatf("id=%0d value=%0d", id, value);
    endfunction
  endclass

  //----------------------------------------------------------------------
  // Subscriber that receives transactions via analysis_imp
  // Extends uvm_component directly to avoid parameterized class issues
  //----------------------------------------------------------------------
  class simple_subscriber extends uvm_component;
    `uvm_component_utils(simple_subscriber)

    // Analysis imp - will be created by parent
    uvm_analysis_imp #(simple_txn, simple_subscriber) analysis_export;
    int received_count = 0;
    int value_sum = 0;

    function new(string name = "", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      // Create analysis_export here - this is safe because simple_subscriber
      // doesn't extend a parameterized class
      analysis_export = new("analysis_export", this);
      $display("[SUB] build_phase completed");
    endfunction

    // Called by analysis_imp when transaction is written
    virtual function void write(simple_txn t);
      received_count++;
      value_sum += t.value;
      $display("[SUB] Received txn: %s (count=%0d, sum=%0d)", t.convert2string(), received_count, value_sum);
    endfunction
  endclass

  //----------------------------------------------------------------------
  // Monitor that sends transactions via analysis_port
  //----------------------------------------------------------------------
  class simple_monitor extends uvm_component;
    `uvm_component_utils(simple_monitor)

    uvm_analysis_port #(simple_txn) ap;
    int send_count = 5;

    function new(string name = "", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      ap = new("ap", this);
      $display("[MON] build_phase completed");
    endfunction

    virtual task run_phase(uvm_phase phase);
      simple_txn txn;
      $display("[MON] run_phase starting");

      for (int i = 0; i < send_count; i++) begin
        txn = new($sformatf("txn_%0d", i));
        txn.id = i;
        txn.value = (i + 1) * 10;  // 10, 20, 30, 40, 50
        #1;  // Some delay
        $display("[MON] Writing txn: %s @ %0t", txn.convert2string(), $time);
        ap.write(txn);
      end
      $display("[MON] run_phase complete");
    endtask
  endclass

  //----------------------------------------------------------------------
  // Environment with monitor and subscriber
  //----------------------------------------------------------------------
  class simple_env extends uvm_env;
    `uvm_component_utils(simple_env)

    simple_monitor monitor;
    simple_subscriber subscriber;

    function new(string name = "", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      monitor = new("monitor", this);
      subscriber = new("subscriber", this);
      $display("[ENV] build_phase completed");
    endfunction

    virtual function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      // Connect monitor's analysis port to subscriber's analysis imp
      monitor.ap.connect(subscriber.analysis_export);
      $display("[ENV] connect_phase - connected monitor.ap to subscriber.analysis_export");
    endfunction
  endclass

  //----------------------------------------------------------------------
  // Test class
  //----------------------------------------------------------------------
  class tlm_test extends uvm_test;
    `uvm_component_utils(tlm_test)

    simple_env env;
    int expected_count = 5;
    int expected_sum = 150;  // 10 + 20 + 30 + 40 + 50

    function new(string name = "tlm_test", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      env = new("env", this);
      $display("[TEST] build_phase completed");
    endfunction

    virtual task run_phase(uvm_phase phase);
      super.run_phase(phase);
      $display("[TEST] run_phase started @ %0t", $time);
      phase.raise_objection(this, "Running test");

      // Wait for monitor to complete
      #10;

      phase.drop_objection(this, "Test complete");
      $display("[TEST] run_phase ended @ %0t", $time);
    endtask

    virtual function void report_phase(uvm_phase phase);
      super.report_phase(phase);
      $display("[TEST] report_phase: subscriber received %0d txns, sum=%0d",
               env.subscriber.received_count, env.subscriber.value_sum);

      if (env.subscriber.received_count == expected_count &&
          env.subscriber.value_sum == expected_sum) begin
        $display("*-* All Finished *-*");
      end else begin
        $display("%%Error: Expected %0d txns with sum=%0d, got %0d txns with sum=%0d",
                 expected_count, expected_sum,
                 env.subscriber.received_count, env.subscriber.value_sum);
        $stop;
      end
    endfunction
  endclass

endpackage

module t;
  import uvm_pkg::*;
  import test_pkg::*;

  initial begin
    // Register types with factory
    simple_txn::type_id::register();
    simple_subscriber::type_id::register();
    simple_monitor::type_id::register();
    simple_env::type_id::register();
    tlm_test::type_id::register();

    // Run the test
    run_test("tlm_test");
  end

endmodule
