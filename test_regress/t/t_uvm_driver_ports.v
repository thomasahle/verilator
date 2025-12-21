// DESCRIPTION: Verilator: Test UVM driver with seq_item_pull_port
//
// Tests the pattern used in axi4_master_driver_proxy where REQ/RSP
// from parent uvm_driver are used in additional ports.
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off WIDTHEXPAND */
/* verilator lint_off WIDTHTRUNC */

`include "uvm_macros.svh"

import uvm_pkg::*;

// Custom transaction
class my_transaction extends uvm_sequence_item;
   `uvm_object_utils(my_transaction)

   rand bit [7:0] data;

   function new(string name = "my_transaction");
      super.new(name);
   endfunction
endclass

// Driver that uses additional ports with inherited REQ/RSP types
// This is the axi4_master_driver_proxy pattern
class my_driver extends uvm_driver #(my_transaction);
   `uvm_component_utils(my_driver)

   // Additional ports using inherited REQ/RSP type params
   // This is what fails in axi4_avip:
   uvm_seq_item_pull_port #(REQ, RSP) extra_port;

   // Also uses REQ/RSP in analysis ports
   uvm_analysis_port #(RSP) extra_rsp_port;

   function new(string name, uvm_component parent);
      super.new(name, parent);
   endfunction

   virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      extra_port = new("extra_port", this);
      extra_rsp_port = new("extra_rsp_port", this);
   endfunction

   virtual task run_phase(uvm_phase phase);
      phase.raise_objection(this);
      `uvm_info("DRIVER", "Driver running", UVM_LOW)
      #10;
      phase.drop_objection(this);
   endtask
endclass

// Simple test
class my_test extends uvm_test;
   `uvm_component_utils(my_test)

   my_driver drv;

   function new(string name, uvm_component parent);
      super.new(name, parent);
   endfunction

   virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      drv = my_driver::type_id::create("drv", this);
   endfunction

   virtual task run_phase(uvm_phase phase);
      phase.raise_objection(this);
      #100;
      `uvm_info("TEST", "Test complete", UVM_LOW)
      phase.drop_objection(this);
   endtask

   virtual function void report_phase(uvm_phase phase);
      $display("[PASS] UVM driver with extra ports works");
      $write("*-* All Finished *-*\n");
   endfunction
endclass

module t;
   initial begin
      run_test("my_test");
   end
endmodule
