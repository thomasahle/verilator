// DESCRIPTION: Verilator: Verilog Test module
//
// Test for class/interface circular dependency with include files
// This mimics the mbits UartTxDriverBfm / UartTxDriverProxy pattern

module t(input logic clk);
   import DriverPkg::*;

   DriverBfm bfm_inst(clk);

   initial begin
      DriverProxy p;
      p = new();
      p.driverBfm = bfm_inst;
      p.data = 42;
      bfm_inst.proxy = p;
      #10;
      p.run();
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
