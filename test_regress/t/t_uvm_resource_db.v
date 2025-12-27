// DESCRIPTION: Verilator: Test UVM resource_db
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test uvm_resource and uvm_resource_db classes

`include "uvm_macros.svh"

module t;
  import uvm_pkg::*;

  // Test uvm_resource class
  task automatic test_resource();
    uvm_resource #(int) int_res;
    uvm_resource #(string) str_res;

    $display("[%0t] test_resource: Starting", $time);

    // Test int resource
    int_res = new("int_resource");
    if (int_res.is_set()) begin
      $display("ERROR: Resource should not be set initially");
      $stop;
    end

    int_res.set(42);
    if (!int_res.is_set()) begin
      $display("ERROR: Resource should be set after set()");
      $stop;
    end
    if (int_res.get() != 42) begin
      $display("ERROR: Expected 42, got %0d", int_res.get());
      $stop;
    end
    $display("[%0t] Int resource: %0d", $time, int_res.read());

    // Test string resource
    str_res = new("str_resource");
    str_res.write("hello");
    if (str_res.read() != "hello") begin
      $display("ERROR: Expected 'hello', got '%s'", str_res.read());
      $stop;
    end
    $display("[%0t] String resource: %s", $time, str_res.read());

    $display("[%0t] test_resource: PASSED", $time);
  endtask

  // Test uvm_resource_db class
  task automatic test_resource_db();
    int int_val;
    string str_val;
    bit found;

    $display("[%0t] test_resource_db: Starting", $time);

    // Set resources
    uvm_resource_db #(int)::set("top.agent", "timeout", 100);
    uvm_resource_db #(int)::set("top.monitor", "threshold", 50);
    uvm_resource_db #(string)::set("top.*", "mode", "active");

    // Get exact match
    found = uvm_resource_db #(int)::get_by_name("top.agent", "timeout", int_val);
    if (!found || int_val != 100) begin
      $display("ERROR: Expected timeout=100, got %0d (found=%0d)", int_val, found);
      $stop;
    end
    $display("[%0t] top.agent.timeout = %0d", $time, int_val);

    // Get another exact match
    found = uvm_resource_db #(int)::get_by_name("top.monitor", "threshold", int_val);
    if (!found || int_val != 50) begin
      $display("ERROR: Expected threshold=50, got %0d", int_val);
      $stop;
    end
    $display("[%0t] top.monitor.threshold = %0d", $time, int_val);

    // Get wildcard match
    found = uvm_resource_db #(string)::get_by_name("top.agent", "mode", str_val);
    if (!found || str_val != "active") begin
      $display("ERROR: Expected mode='active', got '%s'", str_val);
      $stop;
    end
    $display("[%0t] top.agent.mode = %s (wildcard)", $time, str_val);

    // Test read_by_name (returns value directly)
    int_val = uvm_resource_db #(int)::read_by_name("top.agent", "timeout");
    if (int_val != 100) begin
      $display("ERROR: read_by_name expected 100, got %0d", int_val);
      $stop;
    end
    $display("[%0t] read_by_name: %0d", $time, int_val);

    // Test exists
    if (!uvm_resource_db #(int)::exists("top.agent", "timeout")) begin
      $display("ERROR: Resource should exist");
      $stop;
    end
    if (uvm_resource_db #(int)::exists("top.agent", "nonexistent")) begin
      $display("ERROR: Resource should not exist");
      $stop;
    end
    $display("[%0t] exists() works correctly", $time);

    // Test clear
    uvm_resource_db #(int)::clear();
    found = uvm_resource_db #(int)::get_by_name("top.agent", "timeout", int_val);
    if (found) begin
      $display("ERROR: Resource should be cleared");
      $stop;
    end
    $display("[%0t] clear() works correctly", $time);

    $display("[%0t] test_resource_db: PASSED", $time);
  endtask

  initial begin
    $display("=== UVM Resource DB Tests ===");

    test_resource();
    #10;

    test_resource_db();

    $display("\n=== All Tests PASSED ===");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
