// DESCRIPTION: Verilator: Test function call with empty arguments
// Pattern from UVM: type_id::create("name",,context)
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

    // Function with default arguments
    function automatic string create_name(string name, string parent_name = "", string ctx = "");
        if (ctx != "")
            return {ctx, ".", name};
        else if (parent_name != "")
            return {parent_name, ".", name};
        else
            return name;
    endfunction

    initial begin
        string s;

        // Normal call with all arguments
        s = create_name("item", "parent", "ctx");
        $display("Full: %s", s);
        if (s != "ctx.item") $stop;

        // Call with empty middle argument (UVM RAL pattern)
        s = create_name("item",,"ctx");
        $display("Empty middle: %s", s);
        if (s != "ctx.item") $stop;

        // Call with trailing empty argument
        s = create_name("item", "parent",);
        $display("Trailing empty: %s", s);
        if (s != "parent.item") $stop;

        $write("*-* All Finished *-*\n");
        $finish;
    end

endmodule
