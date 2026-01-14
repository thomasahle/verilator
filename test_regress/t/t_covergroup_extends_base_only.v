// DESCRIPTION: Verilator: Test base covergroup only (without extends)
// Test to isolate if the issue is in base or extended covergroup
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off COVERIGN */
module t;
    class base;
        enum {red, green, blue} color;
        covergroup g1 (bit [3:0] a) with function sample(bit b);
            option.weight       = 10;
            option.per_instance = 1;
            coverpoint a;
            coverpoint b;
            c: coverpoint color;
        endgroup
        function new();
            g1 = new(0);
        endfunction
    endclass

    initial begin
        base b;
        b = new();
        b.g1.sample(0);
        b.g1.sample(1);
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
