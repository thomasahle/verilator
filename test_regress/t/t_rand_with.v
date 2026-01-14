// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
    class MyClass;
        rand int data;
        rand int addr;

        constraint c { data inside {[0:255]}; }
    endclass

    MyClass obj;

    initial begin
        obj = new;

        // Basic randomize()
        void'(obj.randomize());
        $display("data=%0d, addr=%0d", obj.data, obj.addr);

        // Randomize with inline constraint
        void'(obj.randomize() with { data < 10; });
        $display("data=%0d (should be <10)", obj.data);

        if (obj.data >= 10) begin
            $display("ERROR: data should be < 10, got %0d", obj.data);
            $stop;
        end

        // Multiple inline constraints
        void'(obj.randomize() with { data > 100; data < 200; addr == 42; });
        $display("data=%0d (should be 100-200), addr=%0d (should be 42)", obj.data, obj.addr);

        if (obj.data <= 100 || obj.data >= 200) begin
            $display("ERROR: data should be 100-200, got %0d", obj.data);
            $stop;
        end
        if (obj.addr != 42) begin
            $display("ERROR: addr should be 42, got %0d", obj.addr);
            $stop;
        end

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
