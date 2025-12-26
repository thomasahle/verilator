// DESCRIPTION: Verilator: Test UVM scoreboard pattern with multiple TLM FIFOs
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test scoreboard pattern similar to axi4_avip

`include "uvm_macros.svh"

package sb_pkg;
  import uvm_pkg::*;

  // Write transaction
  class write_tx extends uvm_sequence_item;
    rand bit [31:0] addr;
    rand bit [31:0] data;
    rand bit [3:0] id;
    `uvm_object_utils(write_tx)
    function new(string name = "write_tx");
      super.new(name);
    endfunction
  endclass

  // Read transaction
  class read_tx extends uvm_sequence_item;
    rand bit [31:0] addr;
    bit [31:0] data;  // Response data
    rand bit [3:0] id;
    `uvm_object_utils(read_tx)
    function new(string name = "read_tx");
      super.new(name);
    endfunction
  endclass

  // Monitor that sends transactions to scoreboard
  class monitor extends uvm_component;
    uvm_analysis_port #(write_tx) write_ap;
    uvm_analysis_port #(read_tx) read_ap;
    `uvm_component_utils(monitor)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      write_ap = new("write_ap", this);
      read_ap = new("read_ap", this);
    endfunction

    // Simulate sending write transaction
    function void send_write(bit [31:0] addr, bit [31:0] data, bit [3:0] id);
      write_tx tx = new("write_tx");
      tx.addr = addr;
      tx.data = data;
      tx.id = id;
      `uvm_info("MON", $sformatf("Sending write: addr=%h data=%h id=%0d", addr, data, id), UVM_MEDIUM)
      write_ap.write(tx);
    endfunction

    // Simulate sending read transaction
    function void send_read(bit [31:0] addr, bit [31:0] data, bit [3:0] id);
      read_tx tx = new("read_tx");
      tx.addr = addr;
      tx.data = data;
      tx.id = id;
      `uvm_info("MON", $sformatf("Sending read: addr=%h data=%h id=%0d", addr, data, id), UVM_MEDIUM)
      read_ap.write(tx);
    endfunction
  endclass

  // Scoreboard with multiple analysis FIFOs
  class scoreboard extends uvm_scoreboard;
    uvm_tlm_analysis_fifo #(write_tx) write_fifo;
    uvm_tlm_analysis_fifo #(read_tx) read_fifo;

    int write_count;
    int read_count;
    int match_count;
    int mismatch_count;

    // Reference memory for checking
    bit [31:0] ref_mem[bit [31:0]];

    `uvm_component_utils(scoreboard)

    function new(string name, uvm_component parent);
      super.new(name, parent);
      write_count = 0;
      read_count = 0;
      match_count = 0;
      mismatch_count = 0;
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      write_fifo = new("write_fifo", this);
      read_fifo = new("read_fifo", this);
    endfunction

    task run_phase(uvm_phase phase);
      fork
        process_writes();
        process_reads();
      join_none
    endtask

    task process_writes();
      write_tx tx;
      forever begin
        write_fifo.get(tx);
        write_count++;
        ref_mem[tx.addr] = tx.data;
        `uvm_info("SB", $sformatf("Stored write[%0d]: addr=%h data=%h", write_count, tx.addr, tx.data), UVM_MEDIUM)
      end
    endtask

    task process_reads();
      read_tx tx;
      bit [31:0] expected;
      forever begin
        read_fifo.get(tx);
        read_count++;
        if (ref_mem.exists(tx.addr)) begin
          expected = ref_mem[tx.addr];
          if (tx.data == expected) begin
            match_count++;
            `uvm_info("SB", $sformatf("Match: addr=%h data=%h", tx.addr, tx.data), UVM_MEDIUM)
          end else begin
            mismatch_count++;
            `uvm_error("SB", $sformatf("Mismatch: addr=%h expected=%h got=%h", tx.addr, expected, tx.data))
          end
        end else begin
          mismatch_count++;
          `uvm_error("SB", $sformatf("Read from unwritten addr=%h", tx.addr))
        end
      end
    endtask

    function void report_phase(uvm_phase phase);
      super.report_phase(phase);
      `uvm_info("SB", $sformatf("Scoreboard Summary: writes=%0d reads=%0d matches=%0d mismatches=%0d",
                                write_count, read_count, match_count, mismatch_count), UVM_NONE)
    endfunction
  endclass

  // Environment
  class env extends uvm_env;
    monitor mon;
    scoreboard sb;
    `uvm_component_utils(env)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      mon = monitor::type_id::create("mon", this);
      sb = scoreboard::type_id::create("sb", this);
    endfunction

    function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      mon.write_ap.connect(sb.write_fifo.analysis_export);
      mon.read_ap.connect(sb.read_fifo.analysis_export);
    endfunction
  endclass

  // Test
  class sb_test extends uvm_test;
    env m_env;
    `uvm_component_utils(sb_test)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      m_env = env::type_id::create("m_env", this);
    endfunction

    task run_phase(uvm_phase phase);
      phase.raise_objection(this);
      `uvm_info("TEST", "Starting scoreboard test", UVM_MEDIUM)

      // Give scoreboard time to start its tasks
      #1;

      // Send some writes
      m_env.mon.send_write(32'h1000, 32'hDEADBEEF, 4'h1);
      #10;
      m_env.mon.send_write(32'h2000, 32'hCAFEBABE, 4'h2);
      #10;
      m_env.mon.send_write(32'h3000, 32'h12345678, 4'h3);
      #10;

      // Send some reads (should match)
      m_env.mon.send_read(32'h1000, 32'hDEADBEEF, 4'h1);
      #10;
      m_env.mon.send_read(32'h2000, 32'hCAFEBABE, 4'h2);
      #10;

      // Allow scoreboard to process
      #20;

      `uvm_info("TEST", $sformatf("Test complete: writes=%0d reads=%0d matches=%0d",
                                  m_env.sb.write_count, m_env.sb.read_count, m_env.sb.match_count), UVM_MEDIUM)
      phase.drop_objection(this);
    endtask

    function void report_phase(uvm_phase phase);
      super.report_phase(phase);
      if (m_env.sb.write_count == 3 && m_env.sb.read_count == 2 && m_env.sb.match_count == 2 && m_env.sb.mismatch_count == 0) begin
        `uvm_info("TEST", "PASS: Scoreboard processed all transactions correctly", UVM_NONE)
        $write("*-* All Finished *-*\n");
      end else begin
        `uvm_error("TEST", $sformatf("FAIL: Expected w=3 r=2 m=2 mm=0, got w=%0d r=%0d m=%0d mm=%0d",
                                     m_env.sb.write_count, m_env.sb.read_count, m_env.sb.match_count, m_env.sb.mismatch_count))
      end
    endfunction
  endclass

endpackage

module t;
  import uvm_pkg::*;
  import sb_pkg::*;

  initial begin
    sb_test::type_id::register();
    run_test("sb_test");
  end
endmodule
