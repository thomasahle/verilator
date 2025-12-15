// DESCRIPTION: Verilator: Verilog Test module
//
// Test SVA always/eventually property operators (IEEE 1800-2017 16.12.7-16.12.9)
// Note: Verilator uses simplified semantics - just checks at current cycle

/* verilator lint_off ASCRANGE */

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

      // Test pattern: overlapping conditions
      a <= (cyc >= 5 && cyc <= 20);
      b <= (cyc >= 5 && cyc <= 25);
      c <= (cyc >= 5 && cyc <= 22);

      if (cyc == 30) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

   // Test always - property holds at every clock tick
   // Simplified: just checks the property at current cycle
   property p_always;
      @(posedge clk)
      a |-> always b;
   endproperty
   assert property(p_always);

   // Test always with range
   property p_always_range;
      @(posedge clk)
      a |-> always [0:5] b;
   endproperty
   assert property(p_always_range);

   // Test s_always with range (strong version)
   property p_s_always;
      @(posedge clk)
      a |-> s_always [0:3] c;
   endproperty
   assert property(p_s_always);

   // Test s_eventually - property eventually holds
   property p_s_eventually;
      @(posedge clk)
      a |-> s_eventually b;
   endproperty
   assert property(p_s_eventually);

   // Test s_eventually with range
   property p_s_eventually_range;
      @(posedge clk)
      a |-> s_eventually [0:10] b;
   endproperty
   assert property(p_s_eventually_range);

   // Test eventually with range (weak version)
   property p_eventually_range;
      @(posedge clk)
      a |-> eventually [0:5] c;
   endproperty
   assert property(p_eventually_range);

   // Cover that always/eventually are parsed and work
   cover property (@(posedge clk) always b);
   cover property (@(posedge clk) s_eventually c);

endmodule
