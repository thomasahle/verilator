// DESCRIPTION: Verilator: Test nested parametric types with multiple params
//
// Tests the exact pattern used in UVM:
// - Parent class with two type parameters (like uvm_driver#(REQ, RSP))
// - Child class using both type params in nested generics
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Transaction classes
class request_item;
   int addr;
   function new();
      addr = 0;
   endfunction
endclass

class response_item;
   int data;
   function new();
      data = 0;
   endfunction
endclass

// Generic port class with two type parameters (like uvm_seq_item_pull_port)
class dual_port #(type T1 = int, type T2 = int);
   T1 item1;
   T2 item2;

   function void set_item1(T1 val);
      item1 = val;
   endfunction

   function void set_item2(T2 val);
      item2 = val;
   endfunction
endclass

// Parent class with two type parameters (like uvm_driver#(REQ, RSP=REQ))
class driver_base #(type REQ = request_item, type RSP = REQ);
   REQ req;
   RSP rsp;

   function new();
      req = new;
      rsp = new;
   endfunction
endclass

// Child class extending parametric parent and using REQ, RSP in nested generic
// This matches the axi4_master_driver_proxy pattern
class my_driver extends driver_base #(request_item, response_item);
   // This is the pattern that fails: using REQ,RSP (from parent) in another generic
   dual_port #(REQ, RSP) port;

   function new();
      super.new();
      port = new;
   endfunction

   function void test();
      port.set_item1(req);
      port.set_item2(rsp);
      $display("Port item1.addr: %0d, item2.data: %0d",
               port.item1.addr, port.item2.data);
   endfunction
endclass

module t;
   my_driver drv;

   initial begin
      drv = new;
      drv.req.addr = 100;
      drv.rsp.data = 200;
      drv.test();

      if (drv.port.item1.addr == 100 && drv.port.item2.data == 200) begin
         $display("[PASS] Multi-param nested parametric type works");
         $write("*-* All Finished *-*\n");
      end else begin
         $display("[FAIL] Multi-param nested parametric type broken");
      end
      $finish;
   end
endmodule
