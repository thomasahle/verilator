// DESCRIPTION: Verilator: Test UVM virtual sequence mechanism
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test virtual sequences with multiple sub-sequencers

`include "uvm_macros.svh"

package vseq_pkg;
  import uvm_pkg::*;

  // Transaction for channel A
  class tx_a extends uvm_sequence_item;
    rand bit [7:0] data;
    `uvm_object_utils(tx_a)
    function new(string name = "tx_a");
      super.new(name);
    endfunction
  endclass

  // Transaction for channel B
  class tx_b extends uvm_sequence_item;
    rand bit [15:0] addr;
    `uvm_object_utils(tx_b)
    function new(string name = "tx_b");
      super.new(name);
    endfunction
  endclass

  // Driver for channel A
  class driver_a extends uvm_component;
    uvm_seq_item_pull_port #(tx_a) seq_item_port;
    int count = 0;
    `uvm_component_utils(driver_a)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      seq_item_port = new("seq_item_port", this);
    endfunction

    task run_phase(uvm_phase phase);
      tx_a req;
      forever begin
        seq_item_port.get_next_item(req);
        `uvm_info("DRV_A", $sformatf("Got tx_a: data=%h", req.data), UVM_MEDIUM)
        #5;
        count++;
        seq_item_port.item_done();
      end
    endtask
  endclass

  // Driver for channel B
  class driver_b extends uvm_component;
    uvm_seq_item_pull_port #(tx_b) seq_item_port;
    int count = 0;
    `uvm_component_utils(driver_b)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      seq_item_port = new("seq_item_port", this);
    endfunction

    task run_phase(uvm_phase phase);
      tx_b req;
      forever begin
        seq_item_port.get_next_item(req);
        `uvm_info("DRV_B", $sformatf("Got tx_b: addr=%h", req.addr), UVM_MEDIUM)
        #5;
        count++;
        seq_item_port.item_done();
      end
    endtask
  endclass

  // Sequencer for channel A
  class sequencer_a extends uvm_sequencer #(tx_a);
    `uvm_component_utils(sequencer_a)
    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction
  endclass

  // Sequencer for channel B
  class sequencer_b extends uvm_sequencer #(tx_b);
    `uvm_component_utils(sequencer_b)
    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction
  endclass

  // Virtual sequencer with handles to both sub-sequencers
  class virtual_sequencer extends uvm_sequencer #(uvm_sequence_item);
    sequencer_a seqr_a;
    sequencer_b seqr_b;
    `uvm_component_utils(virtual_sequencer)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction
  endclass

  // Sequence for channel A
  class seq_a extends uvm_sequence #(tx_a);
    `uvm_object_utils(seq_a)
    function new(string name = "seq_a");
      super.new(name);
    endfunction

    task body();
      tx_a req;
      repeat(3) begin
        req = new("req");
        start_item(req);
        if (!req.randomize()) `uvm_error("SEQ_A", "Randomize failed")
        finish_item(req);
      end
    endtask
  endclass

  // Sequence for channel B
  class seq_b extends uvm_sequence #(tx_b);
    `uvm_object_utils(seq_b)
    function new(string name = "seq_b");
      super.new(name);
    endfunction

    task body();
      tx_b req;
      repeat(2) begin
        req = new("req");
        start_item(req);
        if (!req.randomize()) `uvm_error("SEQ_B", "Randomize failed")
        finish_item(req);
      end
    endtask
  endclass

  // Virtual sequence that runs on virtual sequencer
  class virtual_seq extends uvm_sequence #(uvm_sequence_item);
    `uvm_object_utils(virtual_seq)
    `uvm_declare_p_sequencer(virtual_sequencer)

    seq_a m_seq_a;
    seq_b m_seq_b;

    function new(string name = "virtual_seq");
      super.new(name);
    endfunction

    task body();
      `uvm_info("VSEQ", "Starting virtual sequence", UVM_MEDIUM)

      // Run sequences in parallel on different sub-sequencers
      fork
        begin
          m_seq_a = seq_a::type_id::create("m_seq_a");
          m_seq_a.start(p_sequencer.seqr_a);
          `uvm_info("VSEQ", "seq_a completed", UVM_MEDIUM)
        end
        begin
          m_seq_b = seq_b::type_id::create("m_seq_b");
          m_seq_b.start(p_sequencer.seqr_b);
          `uvm_info("VSEQ", "seq_b completed", UVM_MEDIUM)
        end
      join

      `uvm_info("VSEQ", "Virtual sequence complete", UVM_MEDIUM)
    endtask
  endclass

  // Agent containing driver and sequencer for channel A
  class agent_a extends uvm_component;
    driver_a drv;
    sequencer_a seqr;
    `uvm_component_utils(agent_a)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      drv = driver_a::type_id::create("drv", this);
      seqr = sequencer_a::type_id::create("seqr", this);
    endfunction

    function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      drv.seq_item_port.connect(seqr.seq_item_export);
    endfunction
  endclass

  // Agent containing driver and sequencer for channel B
  class agent_b extends uvm_component;
    driver_b drv;
    sequencer_b seqr;
    `uvm_component_utils(agent_b)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      drv = driver_b::type_id::create("drv", this);
      seqr = sequencer_b::type_id::create("seqr", this);
    endfunction

    function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      drv.seq_item_port.connect(seqr.seq_item_export);
    endfunction
  endclass

  // Environment with virtual sequencer
  class env extends uvm_env;
    agent_a agt_a;
    agent_b agt_b;
    virtual_sequencer vseqr;
    `uvm_component_utils(env)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      agt_a = agent_a::type_id::create("agt_a", this);
      agt_b = agent_b::type_id::create("agt_b", this);
      vseqr = virtual_sequencer::type_id::create("vseqr", this);
    endfunction

    function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      // Connect virtual sequencer to sub-sequencers
      vseqr.seqr_a = agt_a.seqr;
      vseqr.seqr_b = agt_b.seqr;
    endfunction
  endclass

  // Test
  class vseq_test extends uvm_test;
    env m_env;
    `uvm_component_utils(vseq_test)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      m_env = env::type_id::create("m_env", this);
    endfunction

    task run_phase(uvm_phase phase);
      virtual_seq vseq;

      phase.raise_objection(this);
      `uvm_info("TEST", "Starting virtual sequence test", UVM_MEDIUM)

      vseq = virtual_seq::type_id::create("vseq");
      vseq.start(m_env.vseqr);

      `uvm_info("TEST", $sformatf("drv_a count=%0d, drv_b count=%0d",
                                   m_env.agt_a.drv.count, m_env.agt_b.drv.count), UVM_MEDIUM)
      phase.drop_objection(this);
    endtask

    function void report_phase(uvm_phase phase);
      super.report_phase(phase);
      // Verify both drivers received items
      if (m_env.agt_a.drv.count == 3 && m_env.agt_b.drv.count == 2) begin
        `uvm_info("TEST", "PASS: Both channels received expected items", UVM_NONE)
        $write("*-* All Finished *-*\n");
      end else begin
        `uvm_error("TEST", $sformatf("FAIL: Expected drv_a=3, drv_b=2, got drv_a=%0d, drv_b=%0d",
                                      m_env.agt_a.drv.count, m_env.agt_b.drv.count))
      end
    endfunction
  endclass

endpackage

module t;
  import uvm_pkg::*;
  import vseq_pkg::*;

  initial begin
    vseq_test::type_id::register();
    run_test("vseq_test");
  end
endmodule
