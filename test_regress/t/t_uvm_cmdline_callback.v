// DESCRIPTION: Verilator: Test UVM cmdline processor and callbacks
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test uvm_cmdline_processor and uvm_callback classes

`include "uvm_macros.svh"

module t;
  import uvm_pkg::*;

  // Custom callback class
  class my_callback extends uvm_callback;
    `uvm_object_utils(my_callback)

    int call_count = 0;

    function new(string name = "my_callback");
      super.new(name);
    endfunction

    virtual function void do_something(int value);
      call_count++;
      $display("[%0t] my_callback::do_something called with value=%0d (count=%0d)",
               $time, value, call_count);
    endfunction
  endclass

  // Component that uses callbacks
  class my_component extends uvm_component;
    `uvm_component_utils(my_component)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void process_data(int value);
      my_callback cbs[$];
      $display("[%0t] %s: processing value=%0d", $time, get_full_name(), value);

      // Get all registered callbacks
      uvm_callbacks#(my_component, my_callback)::get(this, cbs);

      // Invoke callbacks
      foreach (cbs[i]) begin
        if (cbs[i].is_enabled()) begin
          cbs[i].do_something(value);
        end
      end
    endfunction
  endclass

  // Test cmdline processor
  task automatic test_cmdline();
    uvm_cmdline_processor clp;
    string value;
    string values[$];
    int count;

    $display("[%0t] test_cmdline: Starting", $time);

    // Get singleton instance
    clp = uvm_cmdline_processor::get_inst();
    if (clp == null) begin
      $display("ERROR: get_inst() returned null");
      $stop;
    end
    $display("[%0t] Got cmdline processor instance", $time);

    // Test get_arg_value (will return 0 if no matching args)
    if (clp.get_arg_value("+MY_ARG=", value)) begin
      $display("[%0t] +MY_ARG value: %s", $time, value);
    end else begin
      $display("[%0t] +MY_ARG not specified (expected in test)", $time);
    end

    // Test get_arg_matches
    if (clp.get_arg_matches("+UVM_")) begin
      $display("[%0t] Found +UVM_ arguments", $time);
    end else begin
      $display("[%0t] No +UVM_ arguments found", $time);
    end

    // Test get_test_name
    if (clp.get_test_name(value)) begin
      $display("[%0t] Test name: %s", $time, value);
    end else begin
      $display("[%0t] No test name specified", $time);
    end

    $display("[%0t] test_cmdline: PASSED", $time);
  endtask

  // Test callbacks
  task automatic test_callbacks();
    my_component comp;
    my_callback cb1, cb2;

    $display("[%0t] test_callbacks: Starting", $time);

    // Create component
    comp = new("comp", null);

    // Create callbacks
    cb1 = new("cb1");
    cb2 = new("cb2");

    // Register callbacks with component
    uvm_callbacks#(my_component, my_callback)::add(comp, cb1);
    uvm_callbacks#(my_component, my_callback)::add(comp, cb2);
    $display("[%0t] Registered 2 callbacks", $time);

    // Process data - should invoke both callbacks
    comp.process_data(100);

    if (cb1.call_count != 1 || cb2.call_count != 1) begin
      $display("ERROR: Callbacks not called correctly (cb1=%0d, cb2=%0d)",
               cb1.call_count, cb2.call_count);
      $stop;
    end

    // Disable cb2
    cb2.set_enabled(0);
    $display("[%0t] Disabled cb2", $time);

    // Process again - only cb1 should be called
    comp.process_data(200);

    if (cb1.call_count != 2 || cb2.call_count != 1) begin
      $display("ERROR: Callback disable failed (cb1=%0d, cb2=%0d)",
               cb1.call_count, cb2.call_count);
      $stop;
    end
    $display("[%0t] Verified cb2 was not called when disabled", $time);

    // Re-enable cb2
    cb2.set_enabled(1);
    comp.process_data(300);

    if (cb1.call_count != 3 || cb2.call_count != 2) begin
      $display("ERROR: Callback enable failed (cb1=%0d, cb2=%0d)",
               cb1.call_count, cb2.call_count);
      $stop;
    end
    $display("[%0t] Verified cb2 called after re-enable", $time);

    // Delete cb1
    uvm_callbacks#(my_component, my_callback)::delete(comp, cb1);
    $display("[%0t] Deleted cb1", $time);

    comp.process_data(400);

    if (cb1.call_count != 3 || cb2.call_count != 3) begin
      $display("ERROR: Callback delete failed (cb1=%0d, cb2=%0d)",
               cb1.call_count, cb2.call_count);
      $stop;
    end
    $display("[%0t] Verified cb1 not called after delete", $time);

    $display("[%0t] test_callbacks: PASSED", $time);
  endtask

  initial begin
    $display("=== UVM Cmdline and Callback Tests ===");

    test_cmdline();
    #10;

    test_callbacks();

    $display("\n=== All Tests PASSED ===");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
