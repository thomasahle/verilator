// DESCRIPTION: Verilator: Verilog Test module
//
// Test UVM import when an interface imports from a package that imports UVM.
// This is the mbits-mirafra VIP pattern: BFM interface imports from agent pkg.

// First: A globals package (no UVM)
package GlobalsPkg;
   parameter int WIDTH = 8;
endpackage

// Second: An agent package that imports UVM
package AgentPkg;
   import uvm_pkg::*;
   `include "uvm_macros.svh"
   import GlobalsPkg::*;

   class DriverProxy extends uvm_driver#(uvm_sequence_item);
      `uvm_component_utils(DriverProxy)
      function new(string name = "DriverProxy", uvm_component parent);
         super.new(name, parent);
      endfunction
   endclass
endpackage

// Third: A BFM interface that imports from the agent package
// This triggers std:: package resolution when interface imports a pkg that imports UVM
import GlobalsPkg::*;
interface DriverBFM(input clk);
   import uvm_pkg::*;
   `include "uvm_macros.svh"
   import AgentPkg::DriverProxy;

   DriverProxy driverProxy;

   initial begin
      `uvm_info("DriverBFM", "BFM initialized", UVM_LOW);
   end
endinterface

module t;
   logic clk = 0;
   DriverBFM u_bfm(.clk);

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
