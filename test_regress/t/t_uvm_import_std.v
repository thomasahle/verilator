// DESCRIPTION: Verilator: Verilog Test module
//
// Test that UVM auto-import works with std package

module t;
   import uvm_pkg::*;
   `include "uvm_macros.svh"

   initial begin
      `uvm_info("TEST", "Hello from UVM", UVM_LOW)
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
