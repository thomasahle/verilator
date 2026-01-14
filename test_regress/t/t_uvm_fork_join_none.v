// DESCRIPTION: Verilator: Test UVM fork/join_none patterns
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test fork/join_none patterns used in UVM virtual sequences

`include "uvm_macros.svh"

package fork_pkg;
  import uvm_pkg::*;

  // Simple transaction
  class simple_tx extends uvm_sequence_item;
    rand bit [7:0] data;
    `uvm_object_utils(simple_tx)
    function new(string name = "simple_tx");
      super.new(name);
    endfunction
  endclass

  // Driver
  class simple_driver extends uvm_component;
    uvm_seq_item_pull_port #(simple_tx) seq_item_port;
    int count = 0;
    `uvm_component_utils(simple_driver)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      seq_item_port = new("seq_item_port", this);
    endfunction

    task run_phase(uvm_phase phase);
      simple_tx req;
      forever begin
        seq_item_port.get_next_item(req);
        `uvm_info("DRV", $sformatf("Got tx: data=%h @ %0t", req.data, $time), UVM_MEDIUM)
        #10;
        count++;
        seq_item_port.item_done();
      end
    endtask
  endclass

  // Sequencer
  class simple_sequencer extends uvm_sequencer #(simple_tx);
    `uvm_component_utils(simple_sequencer)
    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction
  endclass

  // Background sequence that runs forever until disabled
  class background_seq extends uvm_sequence #(simple_tx);
    `uvm_object_utils(background_seq)
    int items_sent = 0;

    function new(string name = "background_seq");
      super.new(name);
    endfunction

    task body();
      simple_tx req;
      `uvm_info("BG_SEQ", "Background sequence starting", UVM_MEDIUM)
      forever begin
        req = new("req");
        start_item(req);
        if (!req.randomize()) `uvm_error("BG_SEQ", "Randomize failed")
        finish_item(req);
        items_sent++;
        `uvm_info("BG_SEQ", $sformatf("Sent item %0d @ %0t", items_sent, $time), UVM_MEDIUM)
        if (items_sent >= 5) break;  // Stop after 5 items
      end
      `uvm_info("BG_SEQ", $sformatf("Background sequence done, sent %0d items", items_sent), UVM_MEDIUM)
    endtask
  endclass

  // Foreground sequence
  class foreground_seq extends uvm_sequence #(simple_tx);
    `uvm_object_utils(foreground_seq)
    int items_sent = 0;

    function new(string name = "foreground_seq");
      super.new(name);
    endfunction

    task body();
      simple_tx req;
      `uvm_info("FG_SEQ", "Foreground sequence starting", UVM_MEDIUM)
      repeat(3) begin
        req = new("req");
        start_item(req);
        if (!req.randomize()) `uvm_error("FG_SEQ", "Randomize failed")
        finish_item(req);
        items_sent++;
        `uvm_info("FG_SEQ", $sformatf("Sent item %0d @ %0t", items_sent, $time), UVM_MEDIUM)
      end
      `uvm_info("FG_SEQ", $sformatf("Foreground sequence done, sent %0d items", items_sent), UVM_MEDIUM)
    endtask
  endclass

  // Virtual sequence that uses fork/join_none
  class fork_join_none_seq extends uvm_sequence #(uvm_sequence_item);
    `uvm_object_utils(fork_join_none_seq)
    `uvm_declare_p_sequencer(simple_sequencer)

    background_seq bg_seq;
    foreground_seq fg_seq;

    function new(string name = "fork_join_none_seq");
      super.new(name);
    endfunction

    task body();
      `uvm_info("VSEQ", "Starting fork/join_none test", UVM_MEDIUM)

      // Start background sequence with join_none
      fork
        begin
          bg_seq = background_seq::type_id::create("bg_seq");
          bg_seq.start(p_sequencer);
        end
      join_none

      // Wait a bit for background to start
      #5;

      // Run foreground sequence (this will interleave with background)
      fg_seq = foreground_seq::type_id::create("fg_seq");
      fg_seq.start(p_sequencer);

      // Wait for background to complete
      wait fork;

      `uvm_info("VSEQ", $sformatf("fork/join_none test complete, bg=%0d, fg=%0d",
                                  bg_seq.items_sent, fg_seq.items_sent), UVM_MEDIUM)
    endtask
  endclass

  // Agent
  class simple_agent extends uvm_component;
    simple_driver drv;
    simple_sequencer seqr;
    `uvm_component_utils(simple_agent)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      drv = simple_driver::type_id::create("drv", this);
      seqr = simple_sequencer::type_id::create("seqr", this);
    endfunction

    function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      drv.seq_item_port.connect(seqr.seq_item_export);
    endfunction
  endclass

  // Test
  class fork_test extends uvm_test;
    simple_agent agent;
    `uvm_component_utils(fork_test)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      agent = simple_agent::type_id::create("agent", this);
    endfunction

    task run_phase(uvm_phase phase);
      fork_join_none_seq vseq;

      phase.raise_objection(this);
      `uvm_info("TEST", "Starting fork/join_none test", UVM_MEDIUM)

      vseq = fork_join_none_seq::type_id::create("vseq");
      vseq.start(agent.seqr);

      `uvm_info("TEST", $sformatf("Test complete, driver count=%0d", agent.drv.count), UVM_MEDIUM)
      phase.drop_objection(this);
    endtask

    function void report_phase(uvm_phase phase);
      super.report_phase(phase);
      // Driver should have received 8 items total (5 from bg + 3 from fg)
      if (agent.drv.count == 8) begin
        `uvm_info("TEST", "PASS: Driver received expected 8 items", UVM_NONE)
        $write("*-* All Finished *-*\n");
      end else begin
        `uvm_error("TEST", $sformatf("FAIL: Expected 8 items, got %0d", agent.drv.count))
      end
    endfunction
  endclass

endpackage

module t;
  import uvm_pkg::*;
  import fork_pkg::*;

  initial begin
    fork_test::type_id::register();
    run_test("fork_test");
  end
endmodule
