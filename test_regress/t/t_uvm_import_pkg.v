// DESCRIPTION: Verilator: Verilog Test module
//
// Test UVM import inside a package - ensure std:: types are found

package TestPkg;
   import uvm_pkg::*;
   `include "uvm_macros.svh"
endpackage

module t;
   import TestPkg::*;

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
