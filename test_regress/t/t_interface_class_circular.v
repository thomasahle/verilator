// DESCRIPTION: Verilator: Verilog Test module
//
// Test for forward declaration of class used in interface
// This pattern is common in UVM-based verification environments

// Forward declare the class
typedef class DriverProxy;

// Interface that contains a class instance
interface DriverBfm(input logic clk);
   // Class instance inside interface
   DriverProxy proxy;

   task drive();
      $display("Driving from BFM");
   endtask
endinterface

// Class that contains a virtual interface
class DriverProxy;
   virtual DriverBfm bfm;

   function new();
   endfunction

   task run();
      if (bfm != null) begin
         bfm.drive();
      end
   endtask
endclass

module t(input logic clk);
   DriverBfm bfm_inst(clk);

   initial begin
      DriverProxy p;
      p = new();
      p.bfm = bfm_inst;
      bfm_inst.proxy = p;
      #10;
      p.run();
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
