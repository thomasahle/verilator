// DESCRIPTION: Verilator: Test property/sequence typed ports and local ports

module t(/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   int   cyc = 0;
   logic a = 1'b1;
   logic b = 1'b1;

   always @(posedge clk) begin
      cyc <= cyc + 1;
      a <= 1'b1;
      b <= 1'b1;
      if (cyc == 12) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

   sequence s_base(input logic sig);
      sig;
   endsequence

   sequence s_wrap(sequence s);
      s ##1 s;
   endsequence

   property p_base(input logic sig);
      sig;
   endproperty

   property p_wrap(local int l, property p);
      p;
   endproperty

   property p_seq;
      @(posedge clk) s_wrap(s_base(a));
   endproperty

   property p_prop;
      @(posedge clk) p_wrap(p_base(b));
   endproperty

   assert property (p_seq);
   assert property (p_prop);

endmodule
