// DESCRIPTION: Test SVA until_with and s_until_with operators
// SPDX-License-Identifier: LGPL-3.0-only

module t (/*AUTOARG*/);
   logic clk = 0;
   always #5 clk = ~clk;

   logic valid;
   logic ready;
   int cyc = 0;

   always @(posedge clk) cyc <= cyc + 1;

   // Test stimulus
   initial begin
      valid = 0;
      ready = 0;
   end

   always @(posedge clk) begin
      if (cyc == 5) valid <= 1;
      if (cyc == 10) ready <= 1;
      if (cyc == 11) begin
         valid <= 0;
         ready <= 0;
      end
      if (cyc == 20) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

   // Test s_until_with: valid stays high until and including when ready is high
   property p_valid_s_until_with_ready;
      @(posedge clk) $rose(valid) |-> valid s_until_with ready;
   endproperty
   assert property (p_valid_s_until_with_ready);

   // Test until_with (weak version)
   property p_valid_until_with_ready;
      @(posedge clk) $rose(valid) |-> valid until_with ready;
   endproperty
   assert property (p_valid_until_with_ready);

endmodule
