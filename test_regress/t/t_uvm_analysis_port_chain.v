// DESCRIPTION: Verilator: Test UVM analysis port hierarchical connections
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test port-to-port connections (hierarchical analysis port chains)

`include "uvm_macros.svh"

module t;
  import uvm_pkg::*;

  // Simple transaction class
  class my_txn extends uvm_object;
    `uvm_object_utils(my_txn)
    int value;
    function new(string name = "my_txn");
      super.new(name);
    endfunction
  endclass

  // Inner component with analysis port
  class inner_comp extends uvm_component;
    `uvm_component_utils(inner_comp)

    uvm_analysis_port #(my_txn) analysis_port;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      analysis_port = new("analysis_port", this);
    endfunction

    // Send a transaction
    function void send(int val);
      my_txn txn = new();
      txn.value = val;
      `uvm_info("INNER", $sformatf("Sending value=%0d", val), UVM_MEDIUM)
      analysis_port.write(txn);
    endfunction
  endclass

  // Middle component - has port that connects up and down
  class middle_comp extends uvm_component;
    `uvm_component_utils(middle_comp)

    inner_comp inner;
    uvm_analysis_port #(my_txn) analysis_port;  // Port to parent

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      inner = inner_comp::type_id::create("inner", this);
      analysis_port = new("analysis_port", this);
    endfunction

    virtual function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      // Connect inner's port to our port (port-to-port connection)
      inner.analysis_port.connect(this.analysis_port);
    endfunction
  endclass

  // Outer component - final subscriber
  class outer_comp extends uvm_component;
    `uvm_component_utils(outer_comp)

    middle_comp middle;
    uvm_analysis_imp #(my_txn, outer_comp) analysis_imp;
    int received_values[$];

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      middle = middle_comp::type_id::create("middle", this);
      analysis_imp = new("analysis_imp", this);
    endfunction

    virtual function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      // Connect middle's port to our imp (port-to-imp connection)
      middle.analysis_port.connect(this.analysis_imp);
    endfunction

    // Write function called by analysis_imp
    function void write(my_txn txn);
      `uvm_info("OUTER", $sformatf("Received value=%0d", txn.value), UVM_MEDIUM)
      received_values.push_back(txn.value);
    endfunction
  endclass

  // Test
  class test extends uvm_test;
    `uvm_component_utils(test)

    outer_comp outer;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      outer = outer_comp::type_id::create("outer", this);
    endfunction

    virtual task run_phase(uvm_phase phase);
      phase.raise_objection(this);

      // Send transactions from innermost component
      outer.middle.inner.send(10);
      outer.middle.inner.send(20);
      outer.middle.inner.send(30);

      #10;

      // Verify they were received at the outer level
      if (outer.received_values.size() != 3) begin
        `uvm_error("TEST", $sformatf("Expected 3 values, got %0d", outer.received_values.size()))
      end else if (outer.received_values[0] != 10 ||
                   outer.received_values[1] != 20 ||
                   outer.received_values[2] != 30) begin
        `uvm_error("TEST", "Values don't match")
      end else begin
        `uvm_info("TEST", "PASS: All values received correctly through port chain", UVM_LOW)
      end

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
