// DESCRIPTION: Verilator: Test nested class scope resolution
// Pattern from UVM: OuterClass::nested_class::method()
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

    class OuterClass;
        // Nested class (similar to UVM type_id pattern)
        class type_id;
            static function OuterClass create(string name);
                OuterClass obj = new();
                $display("Created object: %s", name);
                return obj;
            endfunction
        endclass
    endclass

    initial begin
        OuterClass obj;

        // Test double scope resolution: OuterClass::type_id::create
        obj = OuterClass::type_id::create("test_obj");

        if (obj == null) begin
            $display("Error: object is null");
            $stop;
        end

        $write("*-* All Finished *-*\n");
        $finish;
    end

endmodule
