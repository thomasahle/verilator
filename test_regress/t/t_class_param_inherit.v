// DESCRIPTION: Verilator: Test inherited type parameters in parameterized classes
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test that inherited type parameters can be used as type arguments to other classes
// This tests both basic types (int) and class types (like UVM transaction classes)

module t;

  // A transaction class (like uvm_sequence_item)
  class my_transaction;
    int data;
    function new();
      data = 42;
    endfunction
  endclass

  // A simple parameterized container class (like uvm_seq_item_pull_port)
  class container #(type T = my_transaction);
    T item;
    function new();
    endfunction
    function void set_item(T t);
      item = t;
    endfunction
  endclass

  // Base class with type parameters (like uvm_driver #(REQ, RSP))
  class base_class #(type REQ = my_transaction, type RSP = REQ);
    REQ request;
    RSP response;

    function new();
    endfunction
  endclass

  // Test 1: Derived class with basic type (int)
  class derived_basic extends base_class #(int, int);
    container #(REQ) req_container;
    container #(RSP) rsp_container;

    function new();
      super.new();
      req_container = new();
      rsp_container = new();
    endfunction
  endclass

  // Test 2: Derived class with class type (like axi4_master_driver_proxy)
  class derived_class extends base_class #(my_transaction, my_transaction);
    // This pattern matches UVM's axi4_master_driver_proxy
    container #(REQ) req_container;
    container #(RSP) rsp_container;

    function new();
      super.new();
      req_container = new();
      rsp_container = new();
    endfunction

    function void test();
      my_transaction tx = new();
      req_container.set_item(tx);
      rsp_container.set_item(tx);
      $display("req_container.item.data = %0d", req_container.item.data);
      $display("rsp_container.item.data = %0d", rsp_container.item.data);
    endfunction
  endclass

  initial begin
    derived_basic basic_obj;
    derived_class class_obj;

    // Test basic type inheritance
    basic_obj = new();
    basic_obj.req_container.item = 100;
    basic_obj.rsp_container.item = 200;
    $display("basic: req=%0d rsp=%0d", basic_obj.req_container.item, basic_obj.rsp_container.item);

    // Test class type inheritance
    class_obj = new();
    class_obj.test();

    if (basic_obj.req_container.item == 100 &&
        basic_obj.rsp_container.item == 200 &&
        class_obj.req_container.item.data == 42) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end else begin
      $display("FAILED");
      $stop;
    end
  end

endmodule
