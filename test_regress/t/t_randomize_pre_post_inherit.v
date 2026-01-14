// DESCRIPTION: Verilator: Test pre/post_randomize callbacks with inheritance
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0
//
// Tests that pre_randomize and post_randomize are called even when
// defined in a parent class

package test_pkg;
  // Base class with pre/post_randomize callbacks
  class base_item;
    rand bit [7:0] data;
    int pre_count = 0;
    int post_count = 0;

    function void pre_randomize();
      pre_count++;
    endfunction

    function void post_randomize();
      post_count++;
    endfunction
  endclass

  // Derived class without its own callbacks - should inherit parent's
  class derived_item extends base_item;
    rand bit [3:0] extra;
  endclass

  // Multi-level inheritance
  class derived2_item extends derived_item;
    rand bit [1:0] more;
  endclass

  // Derived class with its own callbacks - should use its own
  class override_item extends base_item;
    int override_pre = 0;
    int override_post = 0;

    function void pre_randomize();
      override_pre++;
    endfunction

    function void post_randomize();
      override_post++;
    endfunction
  endclass
endpackage

module t;
  import test_pkg::*;

  initial begin
    int errors = 0;
    base_item b;
    derived_item d;
    derived2_item d2;
    override_item o;

    // Test 1: Base class callbacks work
    b = new;
    void'(b.randomize());
    void'(b.randomize());
    if (b.pre_count != 2) begin
      $display("FAIL: base pre_count=%0d, expected 2", b.pre_count);
      errors++;
    end
    if (b.post_count != 2) begin
      $display("FAIL: base post_count=%0d, expected 2", b.post_count);
      errors++;
    end

    // Test 2: Derived class should call parent's callbacks
    d = new;
    void'(d.randomize());
    void'(d.randomize());
    void'(d.randomize());
    if (d.pre_count != 3) begin
      $display("FAIL: derived pre_count=%0d, expected 3", d.pre_count);
      errors++;
    end
    if (d.post_count != 3) begin
      $display("FAIL: derived post_count=%0d, expected 3", d.post_count);
      errors++;
    end

    // Test 3: Multi-level inheritance should still work
    d2 = new;
    void'(d2.randomize());
    if (d2.pre_count != 1) begin
      $display("FAIL: derived2 pre_count=%0d, expected 1", d2.pre_count);
      errors++;
    end
    if (d2.post_count != 1) begin
      $display("FAIL: derived2 post_count=%0d, expected 1", d2.post_count);
      errors++;
    end

    // Test 4: Overridden callbacks should use child's version
    o = new;
    void'(o.randomize());
    void'(o.randomize());
    if (o.override_pre != 2) begin
      $display("FAIL: override_pre=%0d, expected 2", o.override_pre);
      errors++;
    end
    if (o.override_post != 2) begin
      $display("FAIL: override_post=%0d, expected 2", o.override_post);
      errors++;
    end
    // Parent counters should NOT be incremented when child overrides
    if (o.pre_count != 0) begin
      $display("FAIL: override parent pre_count=%0d, expected 0", o.pre_count);
      errors++;
    end
    if (o.post_count != 0) begin
      $display("FAIL: override parent post_count=%0d, expected 0", o.post_count);
      errors++;
    end

    if (errors == 0) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end else begin
      $display("FAIL: %0d errors", errors);
      $stop;
    end
  end
endmodule
