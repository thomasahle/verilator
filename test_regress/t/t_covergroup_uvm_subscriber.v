// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test class-embedded covergroup with sample(args) in uvm_subscriber pattern

import uvm_pkg::*;
`include "uvm_macros.svh"

module t;
  typedef enum bit[1:0] {MODE0, MODE1, MODE2, MODE3} mode_e;

  class Config;
    mode_e mode;
    int delay;
    function int getDelay();
      return delay;
    endfunction
  endclass

  class Transaction extends uvm_sequence_item;
    int data;
    `uvm_object_utils(Transaction)
    function new(string name = "Transaction");
      super.new(name);
    endfunction
  endclass

  class Coverage extends uvm_subscriber#(Transaction);
    `uvm_component_utils(Coverage)

    Config cfg;

    covergroup cg with function sample(Config c, Transaction t);
      option.per_instance = 1;

      MODE_CP: coverpoint c.mode {
        bins m[] = {[0:3]};
      }

      DELAY_CP: coverpoint c.getDelay() {
        bins d1 = {1};
        bins d2 = {2};
        bins dmore = {[3:$]};
        illegal_bins illegal = {0};
      }

      DATA_CP: coverpoint t.data {
        bins low = {[0:127]};
        bins high = {[128:255]};
      }

      MODE_X_DELAY: cross MODE_CP, DELAY_CP;
    endgroup

    function new(string name = "Coverage", uvm_component parent = null);
      super.new(name, parent);
      cg = new();
    endfunction

    virtual function void write(Transaction t);
      cg.sample(cfg, t);
    endfunction

    function void report_phase(uvm_phase phase);
      $display("Coverage: %0.2f%%", cg.get_inst_coverage());
    endfunction
  endclass

  Coverage cov;
  Config cfg;
  Transaction tx;

  initial begin
    cfg = new;
    tx = new("tx");
    cov = new("cov", null);
    cov.cfg = cfg;

    // Test coverage collection
    cfg.mode = MODE1;
    cfg.delay = 2;
    tx.data = 100;
    cov.write(tx);

    cfg.mode = MODE2;
    cfg.delay = 5;
    tx.data = 200;
    cov.write(tx);

    $display("Coverage after sampling: %0.2f%%", cov.cg.get_inst_coverage());
    if (cov.cg.get_inst_coverage() > 0.0) begin
      $write("*-* All Finished *-*\n");
    end else begin
      $display("ERROR: Coverage should be > 0%%");
    end
    $finish;
  end
endmodule
