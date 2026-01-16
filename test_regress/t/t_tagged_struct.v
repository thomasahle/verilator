// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test tagged unions with struct members (IEEE 1800-2017 7.3.2)
// Tagged unions can contain unpacked struct members - this should lint without error

module t;
    // Tagged union with struct members - should NOT error
    typedef union tagged {
        struct {
            bit [3:0] val1, val2;
        } size_a;
        struct {
            bit [7:0] val1, val2;
        } size_b;
        struct {
            bit [15:0] val1, val2;
        } size_c;
    } sized_data;

    // Nested structs in tagged unions also allowed
    typedef union tagged {
        struct {
            struct {
                bit [7:0] x, y;
            } point;
            bit [7:0] color;
        } colored_point;
        void nothing;
    } nested_union;

    sized_data data;
    nested_union nu;

endmodule
