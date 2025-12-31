// DESCRIPTION: Verilator: Test $unit-scope wildcard import visibility in interfaces
// See IEEE 1800-2017 Section 26.3 about $unit scope
//
// This pattern is used by UVM verification testbenches where parameters
// are defined in a package and imported at $unit scope before interfaces.
//
// This file is part of Verilator.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

package MyParamPkg;
  parameter int MY_DELAY = 16;
  parameter int MY_WIDTH = 8;
endpackage

// Wildcard import at $unit scope - these should be visible in the interface below
import MyParamPkg::*;

interface MyInterface (
  input clk,
  input rst_n
);
  // This should see MY_DELAY from the $unit-scope import
  property p_test;
    @(posedge clk) disable iff (!rst_n)
    $rose(clk) |-> ##[0:MY_DELAY] 1'b1;  // Uses MY_DELAY from package
  endproperty

  assert property (p_test);

  initial begin
    $display("MY_DELAY = %0d", MY_DELAY);
    $display("MY_WIDTH = %0d", MY_WIDTH);
  end
endinterface

module t (/*AUTOARG*/);
  bit clk = 0;
  bit rst_n = 1;

  always #5 clk = ~clk;

  MyInterface myif(.clk(clk), .rst_n(rst_n));

  initial begin
    #100;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
