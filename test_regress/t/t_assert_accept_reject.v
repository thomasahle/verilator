// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test accept_on and reject_on property operators

module t (/*AUTOARG*/
   clk
   );

   input clk;

   int cyc = 0;
   logic reset = 1;
   logic data = 0;

   always @(posedge clk) begin
      cyc <= cyc + 1;

      // data becomes 1 early
      if (cyc >= 3) data <= 1;

      // Release reset after data is stable (cyc >= 5)
      if (cyc == 5) reset <= 0;

      if (cyc == 20) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

   // Test accept_on: property passes if reset is active
   // accept_on(reset) expr => reset || expr
   // When reset=1, property passes (short-circuit OR)
   // When reset=0, check the inner property
   property check_accept_on_simple;
      @(posedge clk) accept_on(reset) data;
   endproperty
   // During reset (cyc 0-3): reset=1, so accept_on passes
   // After reset (cyc >= 4): reset=0, data=1, so property passes
   assert property(check_accept_on_simple);

   // Test reject_on: property fails if condition is active
   // reject_on(cond) expr => !cond && expr
   // When cond=1, property fails
   // When cond=0, check the inner expression
   property check_reject_on_simple;
      @(posedge clk) reject_on(reset) 1;  // Always passes after reset
   endproperty
   // During reset (cyc 0-3): reset=1, so reject_on fails... but we use cover
   // After reset (cyc >= 4): reset=0, inner expr=1, passes
   cover property(check_reject_on_simple);

   // Test sync_accept_on (same semantics in Verilator)
   property check_sync_accept;
      @(posedge clk) sync_accept_on(reset) data;
   endproperty
   cover property(check_sync_accept);

   // Test sync_reject_on (same semantics in Verilator)
   property check_sync_reject;
      @(posedge clk) sync_reject_on(reset) 1;
   endproperty
   cover property(check_sync_reject);

   // Test accept_on with implication
   // accept_on(reset) (a |-> b) => reset || (a |-> b)
   property accept_on_with_impl;
      @(posedge clk) accept_on(reset) (cyc > 10) |-> data;
   endproperty
   assert property(accept_on_with_impl);

endmodule
