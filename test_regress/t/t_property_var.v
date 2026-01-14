// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test property variable declaration parsing

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   int cyc = 0;
   logic valid;
   logic ready;
   int data;

   // Property with local variable declaration
   // Note: Full semantics not implemented, but parsing works
   property p_with_var;
      int x;  // Property local variable
      @(posedge clk) valid |-> ready;
   endproperty
   // Don't assert - just testing parsing
   // assert property (p_with_var);

   // Property with multiple local variables
   property p_multi_var;
      int a, b;
      logic [7:0] c;
      @(posedge clk) valid |-> ready;
   endproperty

   always @(posedge clk) begin
      cyc <= cyc + 1;
      valid <= 1'b1;
      ready <= 1'b1;
      data <= cyc;

      if (cyc == 10) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
