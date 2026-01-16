// DESCRIPTION: Verilator: Test sequence local variables syntax
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// This test verifies that sequence local variables parse and elaborate
// correctly. The actual runtime capture semantics are tested separately.

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   logic [7:0] data;
   logic       valid;
   integer     cyc;

   initial cyc = 0;

   always @(posedge clk) begin
      cyc <= cyc + 1;
      valid <= 1'b1;
      data <= cyc[7:0];
   end

   // Sequence with local variable declaration
   sequence seq_with_local;
      logic [7:0] captured;
      @(posedge clk) (valid, captured = data) ##1 (captured == captured);
   endsequence

   // Property using sequence with local
   property prop_local;
      @(posedge clk) disable iff (cyc < 2)
      seq_with_local;
   endproperty

   // Sequence with clocked body after local var declaration
   sequence seq_clocked_after_local;
      logic [7:0] x;
      @(posedge clk) (1'b1, x = data) ##1 1'b1;
   endsequence

   // Cover the sequences to verify they elaborate
   cover property (@(posedge clk) seq_with_local);
   cover property (@(posedge clk) seq_clocked_after_local);

   // Finish test
   always @(posedge clk) begin
      if (cyc == 10) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
