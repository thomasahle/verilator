// DESCRIPTION: Verilator: Test nested parametric types from parent class
//
// Tests the pattern used in UVM where a child class uses type parameters
// from a parametric parent class in nested generic types.
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Simple transaction class
class my_transaction;
   int data;
   function new();
      data = 0;
   endfunction
endclass

// Generic container class (like uvm_seq_item_pull_port)
class generic_container #(type T = int);
   T item;
   function void set(T val);
      item = val;
   endfunction
   function T get();
      return item;
   endfunction
endclass

// Generic parent class (like uvm_driver#(REQ))
// This defines REQ as a type parameter
class parent_class #(type REQ = my_transaction);
   REQ req;

   function new();
      req = new;
   endfunction
endclass

// Child class that uses parent's REQ type in a nested generic
// This is the pattern that fails in axi4_master_driver_proxy
class child_class extends parent_class #(my_transaction);
   // This should work: using REQ (inherited from parent) in another generic type
   generic_container #(REQ) container;

   function new();
      super.new();
      container = new;
   endfunction

   function void test();
      container.set(req);
      $display("Container item data: %0d", container.get().data);
   endfunction
endclass

module t;
   child_class obj;

   initial begin
      obj = new;
      obj.req.data = 42;
      obj.test();

      if (obj.container.get().data == 42) begin
         $display("[PASS] Nested parametric type works");
         $write("*-* All Finished *-*\n");
      end else begin
         $display("[FAIL] Nested parametric type broken");
      end
      $finish;
   end
endmodule
