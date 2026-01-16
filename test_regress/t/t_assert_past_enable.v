// DESCRIPTION: Verilator: Test $past with enable expression

module t(/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   int   cyc = 0;
   logic a = 0;
   logic en = 0;

   always @(posedge clk) begin
      cyc <= cyc + 1;
      a <= ~a;
      en <= ~en;
      if (cyc == 20) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

   // When enable is high every other cycle, $past(a,1,en) should match $past(a,2).
   property p_past_enable;
      @(posedge clk) disable iff (cyc < 4)
        en |-> ($past(a, 1, en) == $past(a, 2));
   endproperty

   assert property (p_past_enable);

endmodule
