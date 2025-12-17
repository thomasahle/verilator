// DESCRIPTION: Verilator: Verilog Test module
//
// Test UVM import when there are multiple packages, and only some import UVM.
// This reproduces the mbits-mirafra VIP structure where globals packages
// don't import UVM but agent packages do.

// First package - no UVM import (like SpiGlobalsPkg)
package GlobalsPkg;
   parameter int WIDTH = 8;
   parameter int MAX_BITS = 1024;
endpackage

// Second package - imports UVM (like SpiMasterPkg)
package MasterPkg;
   `include "uvm_macros.svh"
   import uvm_pkg::*;
   import GlobalsPkg::*;

   class master_config extends uvm_object;
      rand bit [WIDTH-1:0] data;
      `uvm_object_utils(master_config)
      function new(string name = "master_config");
         super.new(name);
      endfunction
   endclass
endpackage

// Third package - also imports UVM (like SpiSlavePkg)
package SlavePkg;
   `include "uvm_macros.svh"
   import uvm_pkg::*;
   import GlobalsPkg::*;

   class slave_config extends uvm_object;
      rand bit [WIDTH-1:0] data;
      `uvm_object_utils(slave_config)
      function new(string name = "slave_config");
         super.new(name);
      endfunction
   endclass
endpackage

module t;
   import MasterPkg::*;
   import SlavePkg::*;

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
