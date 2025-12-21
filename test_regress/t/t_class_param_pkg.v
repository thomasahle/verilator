// DESCRIPTION: Verilator: Test parametric types in a package context
//
// Tests the pattern used in axi4_avip where:
// - UVM classes are imported into a package
// - User classes extend UVM classes and use inherited type params
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`include "uvm_macros.svh"

// User package that includes classes using UVM
package my_pkg;
   import uvm_pkg::*;

   // Transaction class
   class my_tx extends uvm_sequence_item;
      `uvm_object_utils(my_tx)
      rand bit [7:0] data;
      function new(string name = "my_tx");
         super.new(name);
      endfunction
   endclass

   // Driver class using inherited REQ/RSP in additional ports
   class my_driver extends uvm_driver #(my_tx);
      `uvm_component_utils(my_driver)

      // This is the pattern that fails in axi4_avip
      uvm_seq_item_pull_port #(REQ, RSP) extra_port;
      uvm_analysis_port #(RSP) rsp_port;

      function new(string name, uvm_component parent);
         super.new(name, parent);
      endfunction

      virtual function void build_phase(uvm_phase phase);
         super.build_phase(phase);
         extra_port = new("extra_port", this);
         rsp_port = new("rsp_port", this);
      endfunction
   endclass

endpackage

module t;
   import uvm_pkg::*;
   import my_pkg::*;

   initial begin
      $display("[PASS] Package with parametric types compiles");
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
