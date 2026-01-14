// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test bind with instance list syntax (IEEE 1800-2017 23.11)
// bind module_name : inst1, inst2 bind_instantiation
//
// Note: Currently Verilator parses this syntax but binds to all instances
// of the target module. Per-instance filtering is not yet implemented.

module bind_checker (input wire si);
   initial begin
      $display("bind_checker instantiated with si=%b", si);
   end
endmodule

module target_module (output logic [31:0] so, input si);
   assign so = {32{si}};
endmodule

module t (/*AUTOARG*/);
   wire [31:0] o1, o2;
   wire si1 = 1'b0;
   wire si2 = 1'b1;

   target_module inst1 (.so(o1), .si(si1));
   target_module inst2 (.so(o2), .si(si2));

   // Bind checker to instances using instance list syntax
   bind target_module : inst1, inst2 bind_checker chk (.si(si));

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
