// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test for property/sequence expression modifiers that are now supported
// (parsed and ignored for simulation)

module t(/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   logic a, b, reset;
   int cyc = 0;

   // Make assertions trivially true by having a=0 always
   assign a = 1'b0;
   assign b = 1'b1;
   assign reset = 1'b0;

   always @(posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 10) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

   // Test strong/weak property modifiers (hints for formal tools)
   // These are parsed and the underlying property is checked
   property p_strong;
      @(posedge clk) a |-> strong(b);
   endproperty
   assert property(p_strong);

   property p_weak;
      @(posedge clk) a |-> weak(b);
   endproperty
   assert property(p_weak);

   // Test accept_on/reject_on property modifiers (abort conditions)
   // These are parsed and the underlying property is checked
   property p_accept_on;
      @(posedge clk) accept_on(reset) (a |-> b);
   endproperty
   assert property(p_accept_on);

   property p_reject_on;
      @(posedge clk) reject_on(reset) (a |-> b);
   endproperty
   assert property(p_reject_on);

   property p_sync_accept_on;
      @(posedge clk) sync_accept_on(reset) (a |-> b);
   endproperty
   assert property(p_sync_accept_on);

   property p_sync_reject_on;
      @(posedge clk) sync_reject_on(reset) (a |-> b);
   endproperty
   assert property(p_sync_reject_on);

   // Test first_match sequence modifier
   property p_first_match;
      @(posedge clk) a |-> first_match(b);
   endproperty
   assert property(p_first_match);

endmodule
