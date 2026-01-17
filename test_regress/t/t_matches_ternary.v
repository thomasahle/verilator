// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test that 'matches' operator works correctly in ternary expressions
// without requiring parentheses (grammar precedence fix)

module t;
  typedef union tagged {
    void Invalid;
    int Valid;
  } MaybeInt;

  initial begin
    MaybeInt val;
    MaybeInt val2;
    int result;

    // Test 1: Basic matches in ternary (without parentheses)
    // Previously required: result = (val matches tagged Valid) ? 1 : 0;
    val = tagged Valid 42;
    result = val matches tagged Valid ? 1 : 0;
    if (result !== 1) $stop;

    val = tagged Invalid;
    result = val matches tagged Valid ? 1 : 0;
    if (result !== 0) $stop;

    // Test 2: Matches with Invalid member
    val = tagged Invalid;
    result = val matches tagged Invalid ? 100 : 0;
    if (result !== 100) $stop;

    // Test 3: Nested ternary with matches
    val = tagged Valid 42;
    result = val matches tagged Valid ? (val matches tagged Valid ? 10 : 20) : 30;
    if (result !== 10) $stop;

    val = tagged Invalid;
    result = val matches tagged Valid ? 10 : (val matches tagged Invalid ? 20 : 30);
    if (result !== 20) $stop;

    // Test 4: Multiple matches expressions in same ternary
    val = tagged Valid 5;
    val2 = tagged Valid 10;
    result = val matches tagged Valid ? (val2 matches tagged Valid ? 1 : 2) : 3;
    if (result !== 1) $stop;

    // Test 5: Chained ternary conditions
    val = tagged Valid 42;
    result = val matches tagged Valid ? 1 : val matches tagged Invalid ? 2 : 3;
    if (result !== 1) $stop;

    val = tagged Invalid;
    result = val matches tagged Valid ? 1 : val matches tagged Invalid ? 2 : 3;
    if (result !== 2) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
