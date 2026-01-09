// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test string literal method calls like "123".atoi()

module t;
  initial begin
    // Test atoi on literal
    if ("123".atoi() != 123) $stop;
    if ("  456".atoi() != 456) $stop;
    if ("-789".atoi() != -789) $stop;

    // Test atohex on literal
    if ("FF".atohex() != 255) $stop;
    if ("ABCD".atohex() != 32'hABCD) $stop;

    // Test atooct on literal
    if ("77".atooct() != 63) $stop;

    // Test atobin on literal
    if ("1010".atobin() != 10) $stop;

    // Test len on literal
    if ("Hello".len() != 5) $stop;
    if ("".len() != 0) $stop;

    // Test toupper on literal
    if ("hello".toupper() != "HELLO") $stop;
    if ("HeLLo123".toupper() != "HELLO123") $stop;

    // Test tolower on literal
    if ("HELLO".tolower() != "hello") $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
