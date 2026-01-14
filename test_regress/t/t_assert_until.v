// DESCRIPTION: Verilator: Verilog Test module for until assertion operators
// Test IEEE 1800-2017 property temporal until operators
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   logic valid;
   logic ready;
   logic aresetn;
   integer cnt = 0;

   // Test s_until_with operator - the AXI handshake pattern
   // When valid rises, it must stay asserted until ready
   property axi_valid_stable;
     @(posedge clk) disable iff (!aresetn)
     $rose(valid) |-> valid s_until_with ready;
   endproperty
   AXI_VALID_STABLE_CHECK : assert property (axi_valid_stable);

   // Test until_with operator (non-strong version)
   property p_until_with;
     @(posedge clk) disable iff (!aresetn)
     $rose(valid) |-> valid until_with ready;
   endproperty
   UNTIL_WITH_CHECK : assert property (p_until_with);

   // Test s_until operator (strong without "with")
   property p_s_until;
     @(posedge clk) disable iff (!aresetn)
     valid |-> valid s_until ready;
   endproperty
   S_UNTIL_CHECK : assert property (p_s_until);

   // Test until operator (non-strong without "with")
   property p_until;
     @(posedge clk) disable iff (!aresetn)
     valid |-> valid until ready;
   endproperty
   UNTIL_CHECK : assert property (p_until);

   always @(posedge clk) begin
     cnt <= cnt + 1;

     // Initialize
     if (cnt == 0) begin
       aresetn <= 0;
       valid <= 0;
       ready <= 0;
     end

     // Release reset
     if (cnt == 2) begin
       aresetn <= 1;
     end

     // Start valid
     if (cnt == 5) begin
       valid <= 1;
     end

     // Assert ready while valid is high
     if (cnt == 7) begin
       ready <= 1;
     end

     // Drop both
     if (cnt == 8) begin
       valid <= 0;
       ready <= 0;
     end

     // End test
     if (cnt > 15) begin
       $write("*-* All Finished *-*\n");
       $finish;
     end
   end
endmodule
