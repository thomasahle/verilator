// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test expect property statement parsing (IEEE 1800-2017 16.17)
// Note: Full blocking semantics for expect are not yet implemented

module t (/*AUTOARG*/);

   logic a, b;

   // Simple property without clocking event
   property p_simple;
      a |-> b;
   endproperty

   // Test the expect statement syntax in a task
   // (Concurrent property evaluation not yet supported in procedural contexts)
   task test_expect;
      a = 1;
      b = 1;
      // Syntax check - expect with pass/fail actions
      expect(a && b) $display("Pass");
      else $display("Fail");
   endtask

   initial begin
      a = 1;
      b = 1;
      test_expect();
      $write("*-* All Coverage Points Covered *-*\n");
      $finish;
   end

endmodule
