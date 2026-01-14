// DESCRIPTION: Verilator: Test inherited type parameters with defaults
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test inherited type parameters when only some are specified (like UVM pattern)

module t;

  // A transaction class (like axi4_master_tx)
  class my_transaction;
    int data;
    function new();
      data = 42;
    endfunction
  endclass

  // Container class (like uvm_seq_item_pull_port)
  class container #(type REQ = my_transaction, type RSP = REQ);
    REQ req_item;
    RSP rsp_item;
    function new();
    endfunction
  endclass

  // Base class with default parameter referencing another parameter
  // (like uvm_driver #(type REQ = uvm_sequence_item, type RSP = REQ))
  class base_class #(type REQ = my_transaction, type RSP = REQ);
    REQ request;
    RSP response;
    function new();
    endfunction
  endclass

  // Derived class specifying only one parameter (like axi4_master_driver_proxy)
  // This is the UVM pattern: extends uvm_driver#(my_tx)
  // Where RSP defaults to REQ
  class derived_class extends base_class #(my_transaction);
    // Both REQ and RSP should be my_transaction
    container #(REQ, RSP) my_container;

    function new();
      super.new();
      my_container = new();
    endfunction

    function void test();
      my_transaction tx = new();
      my_container.req_item = tx;
      my_container.rsp_item = tx;
      $display("req_item.data = %0d", my_container.req_item.data);
      $display("rsp_item.data = %0d", my_container.rsp_item.data);
    endfunction
  endclass

  initial begin
    derived_class obj;
    obj = new();
    obj.test();

    if (obj.my_container.req_item.data == 42 &&
        obj.my_container.rsp_item.data == 42) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end else begin
      $display("FAILED");
      $stop;
    end
  end

endmodule
