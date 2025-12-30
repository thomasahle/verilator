// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

// Test that writing to inout/output in a FUNCTION after timing control is still an error.
// (Tasks can now do this, but functions cannot.)

module t;
  bit p = 0;

  initial begin
    p = f1(p);
  end

  // Functions cannot have timing controls with inout writes - this should error
  function automatic bit f1(inout bit p);
    fork
      p = #1 1;  // Error: Writing to inout in function after timing
    join_none
    return p;
  endfunction
endmodule
