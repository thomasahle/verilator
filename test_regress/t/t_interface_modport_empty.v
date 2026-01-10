// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test modport with empty expression syntax: .name()

interface simple_if;
   logic [7:0] data;
   logic       valid;
   logic       ready;

   // Modport with empty expression syntax - .name() means .name(name)
   modport master (
      output .data(),    // .data() is equivalent to .data(data)
      output .valid(),
      input  .ready()
   );

   modport slave (
      input  .data(),
      input  .valid(),
      output .ready()
   );
endinterface

module producer (simple_if.master m);
   initial begin
      m.data = 8'hAB;
      m.valid = 1'b1;
   end
endmodule

module consumer (simple_if.slave s, input clk);
   int cyc = 0;
   always @(posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 0) begin
         s.ready = 1'b1;
      end else if (cyc == 1) begin
         if (s.data == 8'hAB && s.valid == 1'b1) begin
            $write("*-* All Finished *-*\n");
            $finish;
         end else begin
            $write("ERROR: data=%h valid=%b\n", s.data, s.valid);
            $stop;
         end
      end
   end
endmodule

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;
   simple_if intf();

   producer prod(.m(intf.master));
   consumer cons(.s(intf.slave), .clk(clk));
endmodule
