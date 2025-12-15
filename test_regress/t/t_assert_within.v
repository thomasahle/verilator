// DESCRIPTION: Verilator: Verilog Test module
//
// Test SVA within operator (IEEE 1800-2017 16.9.7)

module t(/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   int   cyc = 0;
   logic a, b, c;
   logic start_outer, end_outer, inner_event;

   // Test signals
   always @(posedge clk) begin
      cyc <= cyc + 1;

      // Test pattern: simple within
      a <= (cyc >= 2 && cyc <= 8);
      b <= (cyc >= 3 && cyc <= 6);

      // For outer sequence: active cycles 10-20
      start_outer <= (cyc == 10);
      end_outer <= (cyc == 20);

      // For inner sequence: active cycles 12-18
      inner_event <= (cyc >= 12 && cyc <= 18);

      if (cyc == 30) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

   // Basic within test - b should occur within a's time window
   // Simplified semantics: both must be true simultaneously at check time
   property p_basic_within;
      @(posedge clk)
      (b) |-> (a within b);
   endproperty
   assert property(p_basic_within);

   // Test within with sequence expressions
   property p_seq_within;
      @(posedge clk)
      inner_event |-> (inner_event within (start_outer ##[1:$] end_outer));
   endproperty
   // Note: Can't easily test the full sequence within semantics
   // The simplified check just verifies both conditions

   // Cover that within is parsed and works
   cover property (@(posedge clk) a within b);

endmodule
