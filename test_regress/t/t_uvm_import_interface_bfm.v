// DESCRIPTION: Verilator: Verilog Test module
//
// Test UVM import when a BFM interface imports uvm_pkg and there's also
// a package that imports uvm_pkg. This is the mbits VIP pattern.
// Bug: "Module/etc never assigned a symbol entry?" for std package.

// First: A globals package (no UVM)
package GlobalsPkg;
   parameter int WIDTH = 8;
endpackage

// Second: A BFM interface that imports UVM directly
import GlobalsPkg::*;
interface DriverBFM(input clk);
   import uvm_pkg::*;
   `include "uvm_macros.svh"

   // Test that std::process is available through UVM import
   initial begin
      std::process p = std::process::self();
      `uvm_info("DriverBFM", $sformatf("BFM initialized, process=%p", p), UVM_LOW);
   end
endinterface

// Third: A package that also imports UVM
package AgentPkg;
   `include "uvm_macros.svh"
   import uvm_pkg::*;
   import GlobalsPkg::*;

   class DriverProxy extends uvm_driver#(uvm_sequence_item);
      `uvm_component_utils(DriverProxy)
      function new(string name = "DriverProxy", uvm_component parent);
         super.new(name, parent);
      endfunction
   endclass
endpackage

module t;
   logic clk = 0;
   DriverBFM u_bfm(.clk);
   import AgentPkg::*;

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
