// DESCRIPTION: Verilator: Test self-referential parameterized classes
// This pattern is used in UVM's uvm_reg_predictor where a class uses itself
// as a template parameter
//
// This file is part of Verilator.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

package test_pkg;
  // Base class (like uvm_sequence_item)
  class base_item;
    int data;
  endclass

  // Analysis imp template (like uvm_analysis_imp)
  class analysis_imp #(type T=base_item, type IMP=base_item);
    IMP m_imp;
    function new(IMP imp);
      m_imp = imp;
    endfunction
    function void write(T t);
      // Call analysis_write on the implementation
    endfunction
  endclass

  // Component base class (like uvm_component)
  class component_base;
    string name;
    function new(string n);
      name = n;
    endfunction
  endclass

  // Self-referential parameterized class (like uvm_reg_predictor)
  // The key pattern: uses analysis_imp with itself as a template parameter
  class predictor #(type BUSTYPE = base_item) extends component_base;
    // This is the self-referential pattern that needs to work:
    analysis_imp #(BUSTYPE, predictor #(BUSTYPE)) bus_in;

    function new(string n);
      super.new(n);
      bus_in = new(this);
    endfunction

    function void analysis_write(BUSTYPE t);
      // Process the bus transaction
      $display("Received data: %0d", t.data);
    endfunction
  endclass

  // Another level of self-reference
  class double_predictor #(type BUSTYPE = base_item) extends predictor #(BUSTYPE);
    analysis_imp #(BUSTYPE, double_predictor #(BUSTYPE)) bus_in2;

    function new(string n);
      super.new(n);
      bus_in2 = new(this);
    endfunction
  endclass
endpackage

module t;
  import test_pkg::*;

  initial begin
    base_item item;
    predictor #(base_item) pred;
    double_predictor #(base_item) dpred;

    item = new();
    item.data = 42;

    pred = new("predictor");
    dpred = new("double_predictor");

    // Test the predictor
    pred.analysis_write(item);
    dpred.analysis_write(item);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
