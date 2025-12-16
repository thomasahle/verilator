// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test: option.comment inside coverpoint bins

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;
   int cyc = 0;

   typedef enum {MODE_A, MODE_B, MODE_C, MODE_D} mode_t;
   mode_t mode;
   int data;

   covergroup cg with function sample(mode_t m, int d);
      option.per_instance = 1;

      // Option inside coverpoint
      MODE_CP : coverpoint m {
         option.comment = "Operation mode";
         bins a = {MODE_A};
         bins b = {MODE_B};
         bins c = {MODE_C};
         bins d = {MODE_D};
      }

      // Multiple options inside coverpoint
      DATA_CP : coverpoint d {
         option.comment = "Data values";
         option.weight = 2;
         bins low = {[0:15]};
         bins mid = {[16:31]};
         bins high = {[32:63]};
      }
   endgroup

   cg my_cg;

   initial begin
      my_cg = new();
   end

   always @(posedge clk) begin
      cyc <= cyc + 1;
      mode <= mode_t'(cyc % 4);
      data <= cyc * 3;

      my_cg.sample(mode, data);

      if (cyc == 20) begin
         $display("Coverage = %0.2f%%", my_cg.get_inst_coverage());
         $write("*-* All Coverage Passed *-*\n");
         $finish;
      end
   end

endmodule
