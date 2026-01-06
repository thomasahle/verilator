// DESCRIPTION: Verilator: Test covergroup with sample args at module level
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off COVERIGN */
module t;
    // Covergroup at module level with sample args - should work
    covergroup cg (bit [3:0] a) with function sample(bit b);
        option.per_instance = 1;
        coverpoint a;
        coverpoint b;
    endgroup

    initial begin
        cg c;
        c = new(4'hA);
        c.sample(0);
        c.sample(1);
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
