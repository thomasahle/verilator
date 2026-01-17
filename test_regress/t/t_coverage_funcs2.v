// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

// Test coverage query functions: $get_coverage, $load_coverage_db, $set_coverage_db_name
// IEEE 1800-2017 Section 21.8

module t (/*AUTOARG*/);

   real coverage_val;

   initial begin
      // $get_coverage() - returns real
      coverage_val = $get_coverage();
      $display("get_coverage = %f", coverage_val);
      if (coverage_val != 0.0) $stop;

      // $set_coverage_db_name(filename) - no-op stub
      $set_coverage_db_name("coverage.db");
      $display("set_coverage_db_name called");

      // $load_coverage_db(filename) - no-op stub
      $load_coverage_db("coverage.db");
      $display("load_coverage_db called");

      $write("*-* All Coverage *-*\n");
      $finish;
   end

endmodule
