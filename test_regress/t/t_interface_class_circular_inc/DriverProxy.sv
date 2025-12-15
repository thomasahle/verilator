// Class file - included by package
class DriverProxy;
   // Virtual interface reference - interface defined elsewhere
   virtual DriverBfm driverBfm;
   int data;

   function new();
      data = 0;
   endfunction

   task run();
      if (driverBfm != null) begin
         driverBfm.drive();
      end
   endtask
endclass
