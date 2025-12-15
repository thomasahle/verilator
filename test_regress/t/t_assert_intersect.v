// DESCRIPTION: Verilator: Verilog Test module
//
// Test SVA intersect operator (IEEE 1800-2017 16.9.6)

module t(/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   int   cyc = 0;
   logic a, b, c;

   // Test signals
   always @(posedge clk) begin
      cyc <= cyc + 1;

      // Test pattern: two overlapping conditions
      a <= (cyc >= 5 && cyc <= 15);
      b <= (cyc >= 5 && cyc <= 15);
      c <= (cyc >= 10 && cyc <= 12);

      if (cyc == 30) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

   // Basic intersect test - both must match at the same time
   // Simplified semantics: both must be true simultaneously
   property p_basic_intersect;
      @(posedge clk)
      (a && b) |-> (a intersect b);
   endproperty
   assert property(p_basic_intersect);

   // Test intersect in a sequence context
   property p_seq_intersect;
      @(posedge clk)
      c |-> (c intersect (a && b));
   endproperty
   assert property(p_seq_intersect);

   // Cover that intersect is parsed and works
   cover property (@(posedge clk) a intersect b);

endmodule
