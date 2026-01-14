// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test UVM-style dependent type parameter defaults
// When extending uvm_driver#(my_tx), both REQ and RSP should resolve to my_tx
// because RSP defaults to REQ.

class uvm_sequence_item;
   int id;
endclass

// A parameterized port class (like UVM's uvm_seq_item_pull_port)
class uvm_seq_item_pull_port #(type T1=uvm_sequence_item, type T2=T1);
   T1 item1;
   T2 item2;
endclass

// UVM-style driver with dependent type parameter: RSP defaults to REQ
class uvm_driver #(type REQ=uvm_sequence_item, type RSP=REQ);
   REQ req;
   RSP rsp;

   // This is the critical pattern: using inherited type params to parameterize another class
   uvm_seq_item_pull_port #(REQ, RSP) seq_item_port;

   function void set_req(REQ r);
      req = r;
   endfunction

   function REQ get_req();
      return req;
   endfunction
endclass

// User transaction type
class my_tx extends uvm_sequence_item;
   int data;
endclass

// User driver that extends uvm_driver with only one type argument
// RSP should default to my_tx (because RSP=REQ and REQ=my_tx)
class my_driver extends uvm_driver#(my_tx);
   // These should resolve to my_tx
   REQ local_req;
   RSP local_rsp;

   // CRITICAL: Using inherited type params to parameterize another class in derived class
   // This is the pattern that fails in UVM testbenches
   uvm_seq_item_pull_port #(REQ, RSP) axi_write_seq_item_port;

   function new();
      local_req = new;
      local_rsp = new;
      local_req.data = 42;
      local_rsp.data = 99;
   endfunction

   function int check();
      // Test that we can access my_tx-specific member
      return local_req.data + local_rsp.data;
   endfunction
endclass

module t;
   initial begin
      my_driver drv;
      drv = new;
      if (drv.check() != 141) $stop;
      if (drv.local_req.id != 0) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
