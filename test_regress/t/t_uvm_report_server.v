// DESCRIPTION: Verilator: Test UVM report server functionality
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test uvm_report_server

`include "uvm_macros.svh"

module t;
  import uvm_pkg::*;

  // Test getting the server
  task automatic test_get_server();
    uvm_report_server server1;
    uvm_report_server server2;

    $display("[%0t] test_get_server: Starting", $time);

    server1 = uvm_report_server::get_server();
    if (server1 == null) begin
      $display("ERROR: get_server() returned null");
      $stop;
    end

    server2 = uvm_report_server::get_server();
    if (server1 != server2) begin
      $display("ERROR: get_server() returned different instances");
      $stop;
    end

    $display("[%0t] test_get_server: PASSED", $time);
  endtask

  // Test severity counts
  task automatic test_severity_counts();
    uvm_report_server server;

    $display("[%0t] test_severity_counts: Starting", $time);

    server = uvm_report_server::get_server();

    // Reset counts
    server.reset_severity_counts();

    // Check initial counts are zero
    if (server.get_severity_count(UVM_INFO) != 0 ||
        server.get_severity_count(UVM_WARNING) != 0 ||
        server.get_severity_count(UVM_ERROR) != 0 ||
        server.get_severity_count(UVM_FATAL) != 0) begin
      $display("ERROR: Initial counts not zero");
      $stop;
    end

    // Increment and check
    server.incr_severity_count(UVM_INFO);
    server.incr_severity_count(UVM_INFO);
    server.incr_severity_count(UVM_WARNING);

    if (server.get_severity_count(UVM_INFO) != 2) begin
      $display("ERROR: Info count should be 2, got %0d", server.get_severity_count(UVM_INFO));
      $stop;
    end

    if (server.get_severity_count(UVM_WARNING) != 1) begin
      $display("ERROR: Warning count should be 1, got %0d", server.get_severity_count(UVM_WARNING));
      $stop;
    end

    $display("[%0t] test_severity_counts: PASSED", $time);
  endtask

  // Test ID counts
  task automatic test_id_counts();
    uvm_report_server server;

    $display("[%0t] test_id_counts: Starting", $time);

    server = uvm_report_server::get_server();

    // Check ID doesn't exist initially
    if (server.get_id_count("TEST_ID") != 0) begin
      $display("ERROR: Initial ID count should be 0");
      $stop;
    end

    // Increment ID
    server.incr_id_count("TEST_ID");
    server.incr_id_count("TEST_ID");
    server.incr_id_count("OTHER_ID");

    if (server.get_id_count("TEST_ID") != 2) begin
      $display("ERROR: TEST_ID count should be 2");
      $stop;
    end

    if (server.get_id_count("OTHER_ID") != 1) begin
      $display("ERROR: OTHER_ID count should be 1");
      $stop;
    end

    $display("[%0t] test_id_counts: PASSED", $time);
  endtask

  // Test max quit count
  task automatic test_max_quit_count();
    uvm_report_server server;

    $display("[%0t] test_max_quit_count: Starting", $time);

    server = uvm_report_server::get_server();

    // Check default
    if (server.get_max_quit_count() != 10) begin
      $display("ERROR: Default max quit count should be 10");
      $stop;
    end

    // Set and check
    server.set_max_quit_count(5);
    if (server.get_max_quit_count() != 5) begin
      $display("ERROR: Max quit count should be 5");
      $stop;
    end

    // Reset for other tests
    server.set_max_quit_count(10);
    server.reset_quit_count();

    $display("[%0t] test_max_quit_count: PASSED", $time);
  endtask

  // Test compose_message
  task automatic test_compose_message();
    uvm_report_server server;
    string msg;

    $display("[%0t] test_compose_message: Starting", $time);

    server = uvm_report_server::get_server();

    msg = server.compose_message(UVM_INFO, "test_comp", "TEST", "Hello World", "test.v", 100);
    $display("Composed message: %s", msg);

    if (msg.len() == 0) begin
      $display("ERROR: compose_message returned empty string");
      $stop;
    end

    $display("[%0t] test_compose_message: PASSED", $time);
  endtask

  // Test report_summarize
  task automatic test_report_summarize();
    uvm_report_server server;

    $display("[%0t] test_report_summarize: Starting", $time);

    server = uvm_report_server::get_server();

    // Reset and add some counts
    server.reset_severity_counts();
    server.incr_severity_count(UVM_INFO);
    server.incr_severity_count(UVM_INFO);
    server.incr_severity_count(UVM_INFO);
    server.incr_severity_count(UVM_WARNING);

    // Print summary
    server.report_summarize();

    $display("[%0t] test_report_summarize: PASSED", $time);
  endtask

  initial begin
    $display("=== UVM Report Server Tests ===");

    test_get_server();
    #10;

    test_severity_counts();
    #10;

    test_id_counts();
    #10;

    test_max_quit_count();
    #10;

    test_compose_message();
    #10;

    test_report_summarize();

    $display("\n=== All Tests PASSED ===");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
