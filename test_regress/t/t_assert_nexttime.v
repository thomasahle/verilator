// DESCRIPTION: Verilator: Verilog Test module
//
// Test SVA nexttime property operator (IEEE 1800-2017 16.12.10)
// Note: Verilator uses simplified semantics - nexttime p just checks p

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

   // Test nexttime - simplified semantics: just checks the property
   // When a is true, b should also be true (b covers a's range)
   property p_nexttime;
      @(posedge clk)
      a |-> nexttime b;
   endproperty
   assert property(p_nexttime);

   // Test s_nexttime - strong version (same for simulation)
   property p_s_nexttime;
      @(posedge clk)
      a |-> s_nexttime c;
   endproperty
   assert property(p_s_nexttime);

   // Test nexttime with cycle count
   // Simplified: just checks the property
   property p_nexttime_count;
      @(posedge clk)
      a |-> nexttime[3] b;
   endproperty
   assert property(p_nexttime_count);

   // Test s_nexttime with cycle count
   property p_s_nexttime_count;
      @(posedge clk)
      a |-> s_nexttime[2] c;
   endproperty
   assert property(p_s_nexttime_count);

   // Cover that nexttime is parsed and works
   cover property (@(posedge clk) nexttime b);
   cover property (@(posedge clk) s_nexttime c);
   cover property (@(posedge clk) nexttime[1] b);

endmodule
