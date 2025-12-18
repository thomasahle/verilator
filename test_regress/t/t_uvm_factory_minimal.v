// DESCRIPTION: Verilator: Minimal UVM factory pattern test
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test minimal UVM factory pattern - static method on parameterized class typedef

package factory_pkg;

  // Simplified registry class
  class registry #(type T = int, string Tname = "");
    static function T create(string name);
      T obj;
      obj = new();
      return obj;
    endfunction

    static function string type_name();
      return Tname;
    endfunction
  endclass

endpackage

module t;
  import factory_pkg::*;

  class my_item;
    int value;
    function new();
      value = 42;
    endfunction
  endclass

  // This is what uvm_object_utils generates
  class my_derived extends my_item;
    typedef registry#(my_derived, "my_derived") type_id;

    static function type_id get_type();
      return null;  // Simplified
    endfunction
  endclass

  initial begin
    my_derived obj;

    // This is the pattern that fails: type_id::create()
    obj = my_derived::type_id::create("test");

    if (obj != null && obj.value == 42) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end else begin
      $display("FAILED: obj is null or value wrong");
      $stop;
    end
  end
endmodule
