// DESCRIPTION: Verilator: Verilog Test module
//
// Test for class in package with interface - matching mbits VIP pattern
// This mimics the UartTxDriverBfm / UartTxDriverProxy pattern

package GlobalPkg;
   typedef enum {STATE_IDLE, STATE_RUN} StateEnum;
endpackage

// Package with forward declaration
package DriverPkg;
   import GlobalPkg::*;

   // Forward declare
   typedef class DriverProxy;

   class DriverTransaction;
      int data;
   endclass

   class DriverConfig;
      int baudRate;
   endclass

   class DriverProxy;
      virtual DriverBfm driverBfm;
      DriverConfig config_h;
      DriverTransaction tx;

      function new();
         config_h = new();
         tx = new();
      endfunction

      task run();
         if (driverBfm != null) begin
            driverBfm.drive(tx);
         end
      endtask
   endclass
endpackage

import GlobalPkg::*;

// Interface that imports the package and uses the class
interface DriverBfm(input logic clk);
   import DriverPkg::*;

   StateEnum state;
   DriverProxy proxy;

   task drive(DriverTransaction tx);
      $display("Driving data: %0d", tx.data);
   endtask
endinterface

module t(input logic clk);
   import DriverPkg::*;

   DriverBfm bfm_inst(clk);

   initial begin
      DriverProxy p;
      p = new();
      p.driverBfm = bfm_inst;
      p.tx.data = 42;
      bfm_inst.proxy = p;
      #10;
      p.run();
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
