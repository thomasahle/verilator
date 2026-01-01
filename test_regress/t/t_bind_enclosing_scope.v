// DESCRIPTION: Verilator: Test bind with signals from enclosing scope
//
// This tests bind statements that reference signals from the enclosing
// module's scope (not the bound-to module's scope).
//
// This pattern is used in JTAG AVIP and other testbenches.

// Interface
interface my_if(input logic clk);
   logic data;
   logic reset;
endinterface

// Module that will be bound to
module inner_module(
   input logic clk,
   input logic data,
   input logic reset
);
   // Some logic
   always_ff @(posedge clk) begin
      if (reset) begin
         // reset logic
      end
   end
endmodule

// Assertions module to bind
module my_assertions(
   input logic clk,
   input logic data,
   input logic reset
);
   // Simple assertion
   property p_data_stable;
      @(posedge clk) disable iff (reset)
      data |-> ##1 data;
   endproperty

   assert property (p_data_stable);
endmodule

// Outer module that instantiates inner_module and has interface port
module outer_module(my_if intf);
   // Instantiate inner module
   inner_module inner(
      .clk(intf.clk),
      .data(intf.data),
      .reset(intf.reset)
   );

   // This bind uses MODULE TYPE name (not instance name) and references
   // signals from enclosing scope - this is the problematic pattern from JTAG AVIP
   bind inner_module my_assertions my_asserts(
      .clk(intf.clk),     // Reference to enclosing scope's interface port
      .data(intf.data),
      .reset(intf.reset)
   );
endmodule

// Top module (named 't' for test harness compatibility)
module t;
   logic clk = 0;
   always #5 clk = ~clk;

   my_if intf(clk);

   int cyc = 0;

   // Reset and data
   initial begin
      intf.reset = 1;
      intf.data = 0;
   end

   always @(posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 2) begin
         intf.reset <= 0;
      end
      if (cyc == 4) begin
         intf.data <= 1;
      end
      if (cyc > 10) begin
         $write("*-* All Coverage *-*\n");
         $finish;
      end
   end

   // Instantiate outer module
   outer_module outer(.intf(intf));
endmodule
