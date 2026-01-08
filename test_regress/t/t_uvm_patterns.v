// DESCRIPTION: Verilator: Test comprehensive UVM patterns
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0
//
// Tests key UVM patterns that are commonly used in testbenches

package uvm_patterns_pkg;

  // Base class with randomization
  class uvm_sequence_item;
    rand bit [7:0] addr;
    rand bit [7:0] data;
    int pre_count = 0;
    int post_count = 0;

    function void pre_randomize();
      pre_count++;
    endfunction

    function void post_randomize();
      post_count++;
    endfunction

    constraint c_addr { addr inside {[0:127]}; }
  endclass

  // Extended class with super calls
  class my_transaction extends uvm_sequence_item;
    rand bit [3:0] cmd;

    function new();
      super.new();
    endfunction

    constraint c_cmd { cmd != 4'hF; }
  endclass

  // Sequence class demonstrating UVM patterns
  class my_sequence;
    my_transaction req;
    int pass_count = 0;

    task body();
      req = new;

      // Pattern 1: Basic randomize
      if (req.randomize()) pass_count++;

      // Pattern 2: randomize() with inline constraints
      if (req.randomize() with { data > 8'd50; }) begin
        if (req.data > 50) pass_count++;
      end

      // Pattern 3: randomize(var_list)
      if (req.randomize(addr)) pass_count++;

      // Pattern 4: do-while randomize pattern
      do begin
        void'(req.randomize());
      end while (req.data < 10);
      if (req.data >= 10) pass_count++;
    endtask
  endclass

endpackage

module t;
  import uvm_patterns_pkg::*;

  // Covergroup test
  bit [3:0] cov_val;

  covergroup cg;
    cp_val: coverpoint cov_val {
      bins low = {[0:7]};
      bins high = {[8:15]};
      wildcard bins even = {4'b???0};
    }
  endgroup

  cg cg_inst = new;

  initial begin
    my_sequence seq = new;
    int errors = 0;

    // Test sequence patterns
    seq.body();
    if (seq.pass_count != 4) begin
      $display("FAIL: sequence pass_count=%0d, expected 4", seq.pass_count);
      errors++;
    end

    // Test pre/post_randomize callbacks
    if (seq.req.pre_count == 0 || seq.req.post_count == 0) begin
      $display("FAIL: pre/post_randomize not called");
      errors++;
    end

    // Test super.new() inheritance
    if (seq.req.addr > 127) begin
      $display("FAIL: constraint from base class not working");
      errors++;
    end

    // Test covergroup
    for (int i = 0; i < 16; i++) begin
      cov_val = 4'(i);
      cg_inst.sample();
    end
    if (cg_inst.get_coverage() != 100.0) begin
      $display("FAIL: coverage=%0.2f%%, expected 100%%", cg_inst.get_coverage());
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
