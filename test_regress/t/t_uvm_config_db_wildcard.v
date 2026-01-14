// DESCRIPTION: Verilator: UVM config_db wildcard pattern matching test
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // Test config type
  class my_config extends uvm_object;
    int value;

    function new(string name = "my_config");
      super.new(name);
    endfunction

    function string get_type_name();
      return "my_config";
    endfunction
  endclass

  // Inner component - will receive config via wildcard
  class inner_agent extends uvm_component;
    my_config cfg;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      if (!uvm_config_db#(my_config)::get(this, "", "my_config", cfg)) begin
        `uvm_fatal("INNER", "Failed to get my_config from config_db")
      end
      `uvm_info("INNER", $sformatf("Got config with value=%0d", cfg.value), UVM_LOW)
    endfunction

    function string get_type_name();
      return "inner_agent";
    endfunction
  endclass

  // Middle component
  class middle_env extends uvm_component;
    inner_agent agent;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      agent = new("agent", this);
      agent.build_phase(phase);
    endfunction

    function string get_type_name();
      return "middle_env";
    endfunction
  endclass

  // Outer test component
  class outer_test extends uvm_component;
    middle_env env;
    my_config cfg;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);

      // Create and configure
      cfg = new("my_config");
      cfg.value = 42;

      // Set config using wildcard pattern "*agent*" - should match env.agent
      // This is the pattern used by APB AVIP: set(this, "*master_agent*", "config", cfg)
      uvm_config_db#(my_config)::set(this, "*agent*", "my_config", cfg);

      // Build children
      env = new("env", this);
      env.build_phase(phase);
    endfunction

    function string get_type_name();
      return "outer_test";
    endfunction
  endclass

  // Additional test for different wildcard patterns
  class pattern_test extends uvm_component;
    my_config cfg1, cfg2, cfg3;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
      my_config retrieved;

      super.build_phase(phase);

      // Create configs
      cfg1 = new("cfg1"); cfg1.value = 100;
      cfg2 = new("cfg2"); cfg2.value = 200;
      cfg3 = new("cfg3"); cfg3.value = 300;

      // Test 1: Exact match
      uvm_config_db#(my_config)::set(this, "exact_path", "field1", cfg1);
      if (!uvm_config_db#(my_config)::get(this, "exact_path", "field1", retrieved)) begin
        `uvm_fatal("TEST", "Exact match failed")
      end
      if (retrieved.value != 100) `uvm_fatal("TEST", "Wrong value for exact match")
      `uvm_info("TEST", "Exact match PASSED", UVM_LOW)

      // Test 2: Wildcard suffix (*) - should match any depth
      uvm_config_db#(my_config)::set(this, "*", "field2", cfg2);
      if (!uvm_config_db#(my_config)::get(this, "a.b.c.d", "field2", retrieved)) begin
        `uvm_fatal("TEST", "Wildcard * match failed")
      end
      if (retrieved.value != 200) `uvm_fatal("TEST", "Wrong value for wildcard *")
      `uvm_info("TEST", "Wildcard * match PASSED", UVM_LOW)

      // Test 3: Contains pattern (*foo*)
      uvm_config_db#(my_config)::set(this, "*special*", "field3", cfg3);
      if (!uvm_config_db#(my_config)::get(this, "a.special_thing.b", "field3", retrieved)) begin
        `uvm_fatal("TEST", "Contains pattern *special* match failed")
      end
      if (retrieved.value != 300) `uvm_fatal("TEST", "Wrong value for *special*")
      `uvm_info("TEST", "Contains pattern *special* PASSED", UVM_LOW)

      `uvm_info("TEST", "All pattern tests PASSED", UVM_LOW)
    endfunction

    function string get_type_name();
      return "pattern_test";
    endfunction
  endclass

  uvm_phase m_phase;
  outer_test test;
  pattern_test ptest;
  int pass_count;

  initial begin
    m_phase = new("build");
    pass_count = 0;

    $display("=== Testing uvm_config_db wildcard pattern matching ===");

    // Test 1: Hierarchical wildcard matching (APB AVIP pattern)
    $display("\n--- Test 1: Hierarchical wildcard *agent* pattern ---");
    test = new("uvm_test_top", null);
    test.build_phase(m_phase);
    // If we get here without fatal, it passed
    $display("Test 1 PASSED: *agent* matched env.agent");
    pass_count++;

    // Test 2: Various pattern tests
    $display("\n--- Test 2: Various pattern tests ---");
    ptest = new("pattern_test", null);
    ptest.build_phase(m_phase);
    $display("Test 2 PASSED: All pattern tests completed");
    pass_count++;

    $display("\n=== All %0d tests PASSED ===", pass_count);
    $write("*-* All Coverage Tests Passed *-*\n");
    $finish;
  end
endmodule
