// Interface that imports the package and uses the class
import DriverPkg::*;

interface DriverBfm(input logic clk);
   // Class instance inside interface - creates circular dependency
   DriverProxy proxy;

   task drive();
      $display("Driving from BFM, data=%0d", proxy.data);
   endtask
endinterface
