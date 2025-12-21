// DESCRIPTION: Verilator: Test using inherited type parameters in nested generics
//
// Tests the exact UVM pattern where:
// 1. Parent class defines type parameters (REQ, RSP)
// 2. Child class extends with concrete types
// 3. Child class uses inherited type params (not its own) in nested generics
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Transaction class
class my_tx;
   int data;
   function new();
      data = 0;
   endfunction
endclass

// Generic port class (like uvm_seq_item_pull_port)
class port_class #(type T1 = int, type T2 = T1);
   T1 req_item;
   T2 rsp_item;
endclass

// Parent class with type parameters (like uvm_driver#(REQ, RSP=REQ))
class base_driver #(type REQ = my_tx, type RSP = REQ);
   // Port in parent - this works
   port_class #(REQ, RSP) parent_port;

   function new();
   endfunction
endclass

// Child class extending with concrete type, using inherited REQ/RSP in nested generic
// This is the exact axi4_master_driver_proxy pattern
class child_driver extends base_driver #(my_tx);
   // Use inherited REQ, RSP type params in a new nested generic
   // This is what fails in UVM: uvm_seq_item_pull_port #(REQ,RSP) axi_write_seq_item_port;
   port_class #(REQ, RSP) child_port;

   REQ req;
   RSP rsp;

   function new();
      super.new();
   endfunction

   virtual function void build();
      parent_port = new;
      child_port = new;
      req = new;
      rsp = new;
   endfunction

   function void test();
      child_port.req_item = req;
      child_port.rsp_item = rsp;
      req.data = 42;
      $display("child_port.req_item.data = %0d", child_port.req_item.data);
   endfunction
endclass

module t;
   child_driver drv;

   initial begin
      drv = new;
      drv.build();
      drv.test();

      if (drv.child_port.req_item.data == 42) begin
         $display("[PASS] Inherited type params work in nested generics");
         $write("*-* All Finished *-*\n");
      end else begin
         $display("[FAIL] Inherited type params broken");
      end
      $finish;
   end
endmodule
