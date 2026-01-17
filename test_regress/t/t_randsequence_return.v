// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2025 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// Test randsequence production function return values (IEEE 1800-2017 18.17)

// verilog_format: off
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);
// verilog_format: on

module t;

  int result;
  int total;

  initial begin
    // Production function with return - can set external variable via code block
    result = 0;
    // verilator lint_off IGNOREDRETURN
    randsequence(main)
      main : set_result;
      int set_result : { result = 42; return result; };
    endsequence
    // verilator lint_on IGNOREDRETURN
    `checkd(result, 42);

    // Multiple production functions with return values that modify state
    total = 0;
    for (int i = 0; i < 10; ++i) begin
      // verilator lint_off IGNOREDRETURN
      randsequence(main)
        main : add_ten add_five;
        int add_ten : { total += 10; return total; };
        int add_five : { total += 5; return total; };
      endsequence
      // verilator lint_on IGNOREDRETURN
    end
    `checkd(total, 150);  // 10 iterations * (10 + 5) = 150

    // Production function with arguments and return value
    result = 0;
    // verilator lint_off IGNOREDRETURN
    randsequence(main)
      main : multiply(7, 6);
      int multiply(int a, int b) : { result = a * b; return result; };
    endsequence
    // verilator lint_on IGNOREDRETURN
    `checkd(result, 42);

    // Nested production calls - void outer calling int inner
    result = 0;
    // verilator lint_off IGNOREDRETURN
    randsequence(main)
      main : outer;
      void outer : inner { result += 10; };
      int inner : { result = 32; return result; };
    endsequence
    // verilator lint_on IGNOREDRETURN
    `checkd(result, 42);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
