// DESCRIPTION: Verilator: Test coverpoint member access (.cp.get_inst_coverage())
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0
//
// Tests that individual coverpoint coverage can be queried via member access

class my_cg;
  covergroup cg;
    cp1: coverpoint x { bins b1 = {0}; bins b2 = {1}; }
    cp2: coverpoint y { bins b1 = {0}; bins b2 = {1}; }
  endgroup

  int x, y;
  function new; cg = new; endfunction
endclass

module t;
  my_cg c;

  initial begin
    int errors = 0;
    real cp1_cov, cp2_cov, cg_cov;

    c = new;

    // Initially no samples
    cg_cov = c.cg.get_inst_coverage();
    if (cg_cov != 0.0) begin
      $display("FAIL: initial cg coverage=%0.2f, expected 0", cg_cov);
      errors++;
    end

    // Sample x=0 and x=1 (both bins hit for cp1)
    c.x = 0; c.cg.sample();
    c.x = 1; c.cg.sample();

    // y was never set, defaults to 0 (one bin hit for cp2)

    cg_cov = c.cg.get_inst_coverage();
    cp1_cov = c.cg.cp1.get_inst_coverage();
    cp2_cov = c.cg.cp2.get_inst_coverage();

    // cp1 should be 100% (2/2 bins hit)
    if (cp1_cov != 100.0) begin
      $display("FAIL: cp1 coverage=%0.2f, expected 100.0", cp1_cov);
      errors++;
    end

    // cp2 should be 50% (1/2 bins hit - y=0 was sampled)
    if (cp2_cov != 50.0) begin
      $display("FAIL: cp2 coverage=%0.2f, expected 50.0", cp2_cov);
      errors++;
    end

    // Whole covergroup should be 75% (3/4 bins hit)
    if (cg_cov != 75.0) begin
      $display("FAIL: cg coverage=%0.2f, expected 75.0", cg_cov);
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
