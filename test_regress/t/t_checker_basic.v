// DESCRIPTION: Verilator: Test checker declarations and instantiation

package pkg;
  checker my_checker(input logic clk, input logic sig);
    int cnt = 0;
    always @(posedge clk) begin
      cnt <= cnt + 1;
    end

    property p_ok;
      @(posedge clk) sig;
    endproperty
    assert property (p_ok);
  endchecker
endpackage

module t(/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   int   cyc = 0;
   logic sig = 1'b1;

   always @(posedge clk) begin
      cyc <= cyc + 1;
      sig <= 1'b1;
      if (cyc == 8) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

   my_checker chk(.clk(clk), .sig(sig));

endmodule
