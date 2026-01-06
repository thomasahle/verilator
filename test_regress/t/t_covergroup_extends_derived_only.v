// DESCRIPTION: Verilator: Test covergroup extends with only derived class members
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off COVERIGN */
module t;
    class base;
        bit b;
        covergroup g1;
            option.per_instance = 1;
            coverpoint b;
        endgroup
        function new();
            g1 = new();
        endfunction
    endclass

    class derived extends base;
        bit d;
        covergroup extends g1;
            coverpoint d;  // Only derived class member
        endgroup :g1
        function new();
            super.new();
        endfunction
    endclass

    initial begin
        derived obj;
        obj = new();
        obj.b = 0;
        obj.d = 0;
        obj.g1.sample();
        obj.b = 1;
        obj.d = 1;
        obj.g1.sample();
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
