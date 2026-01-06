// DESCRIPTION: Verilator: Test covergroup with only sample args (no constructor args)
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off COVERIGN */
module t;
    // Covergroup with only sample args, no constructor args
    covergroup cg with function sample(bit [3:0] a, bit b);
        option.per_instance = 1;
        coverpoint a;
        coverpoint b;
    endgroup

    initial begin
        cg c;
        c = new();
        c.sample(4'hA, 0);
        c.sample(4'hB, 1);
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
