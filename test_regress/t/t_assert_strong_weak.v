// DESCRIPTION: Verilator: Verilog Test module
//
// Test SVA strong/weak sequence qualifiers (IEEE 1800-2017 16.12.1)

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

      // Test pattern: overlapping conditions for valid implications
      a <= (cyc >= 10 && cyc <= 15);  // a is subset of b's range
      b <= (cyc >= 5 && cyc <= 20);   // b covers a's range
      c <= (cyc >= 10 && cyc <= 15);  // c same as a

      if (cyc == 30) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

   // Test strong() - sequence must complete (for formal verification)
   // For simulation, this is essentially a no-op
   property p_strong;
      @(posedge clk)
      a |-> strong(b);
   endproperty
   assert property(p_strong);

   // Test weak() - sequence allowed to match infinitely
   // For simulation, this is essentially a no-op
   property p_weak;
      @(posedge clk)
      a |-> weak(b);
   endproperty
   assert property(p_weak);

   // Test strong with more complex sequence
   property p_strong_seq;
      @(posedge clk)
      a |-> strong(b && c);
   endproperty
   assert property(p_strong_seq);

   // Test weak with more complex sequence
   property p_weak_seq;
      @(posedge clk)
      c |-> weak(a && b);
   endproperty
   assert property(p_weak_seq);

   // Cover that strong/weak are parsed and work
   cover property (@(posedge clk) strong(a));
   cover property (@(posedge clk) weak(b));

endmodule
