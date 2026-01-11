// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test for bind directive with instance list syntax
// IEEE 1800-2017 Section 23.11

module t;
   target t1();
   target t2();

   initial begin
      // The bind should have added checkers to both instances
      // Check that the bound signals are accessible
      if (t1.check_inst.sig_copy !== t1.sig) $stop;
      if (t2.check_inst.sig_copy !== t2.sig) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

module target;
   logic sig = 1'b1;
endmodule

module checker_mod(input logic sig);
   logic sig_copy;
   assign sig_copy = sig;
endmodule

// Bind using instance list syntax - should bind to both t1 and t2
// Note: Currently binds to all instances (per-instance filtering not yet implemented)
bind target : t1, t2 checker_mod check_inst(.sig(sig));
