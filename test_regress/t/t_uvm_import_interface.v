// DESCRIPTION: Verilator: Verilog Test module
//
// Test UVM import inside interface - reproduces std package bug

package TestPkg;
   parameter int WIDTH = 8;
endpackage

import TestPkg::*;  // Module-level import

interface TestAssertions (
   input clk
);
   import uvm_pkg::*;  // Interface-level import - causes std package error
endinterface

module t;
   logic clk = 0;
   TestAssertions u_assert(.clk);

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
