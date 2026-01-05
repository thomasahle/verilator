// DESCRIPTION: Verilator: Test dual-FIFO scoreboard pattern for bidirectional protocols
// This pattern is used in AVIPs like SPI where master and slave have separate transactions
// that need to be synchronized and compared in a scoreboard
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define UVM_NO_DPI
`define UVM_REGEX_NO_DPI

module t;
   import uvm_pkg::*;
   `include "uvm_macros.svh"

   // Master transaction (what master sends)
   class master_tx extends uvm_sequence_item;
      `uvm_object_utils(master_tx)

      bit [7:0] mosi_data;  // Master Out Slave In
      bit [3:0] addr;

      function new(string name = "master_tx");
         super.new(name);
      endfunction

      virtual function string convert2string();
         return $sformatf("MASTER: addr=%h mosi=%h", addr, mosi_data);
      endfunction
   endclass

   // Slave transaction (what slave receives/responds)
   class slave_tx extends uvm_sequence_item;
      `uvm_object_utils(slave_tx)

      bit [7:0] miso_data;  // Master In Slave Out
      bit [3:0] addr;

      function new(string name = "slave_tx");
         super.new(name);
      endfunction

      virtual function string convert2string();
         return $sformatf("SLAVE: addr=%h miso=%h", addr, miso_data);
      endfunction
   endclass

   // Dual-FIFO Scoreboard - receives from both master and slave monitors
   class dual_scoreboard extends uvm_scoreboard;
      `uvm_component_utils(dual_scoreboard)

      // Separate FIFOs for master and slave transactions
      uvm_tlm_analysis_fifo #(master_tx) master_fifo;
      uvm_tlm_analysis_fifo #(slave_tx) slave_fifo;

      // Comparison statistics
      int compare_pass;
      int compare_fail;
      int master_only;
      int slave_only;

      function new(string name = "", uvm_component parent = null);
         super.new(name, parent);
         compare_pass = 0;
         compare_fail = 0;
         master_only = 0;
         slave_only = 0;
      endfunction

      function void build_phase(uvm_phase phase);
         super.build_phase(phase);
         master_fifo = new("master_fifo", this);
         slave_fifo = new("slave_fifo", this);
      endfunction

      task run_phase(uvm_phase phase);
         master_tx mtx;
         slave_tx stx;

         phase.raise_objection(this);

         // Wait for transactions to arrive
         #5;

         // Process all paired transactions
         while (master_fifo.used() > 0 && slave_fifo.used() > 0) begin
            // Blocking get from both FIFOs
            master_fifo.get(mtx);
            slave_fifo.get(stx);

            // Compare addresses (should match for paired transactions)
            if (mtx.addr == stx.addr) begin
               `uvm_info(get_type_name(),
                  $sformatf("MATCH: %s <-> %s", mtx.convert2string(), stx.convert2string()),
                  UVM_LOW)
               compare_pass++;
            end else begin
               `uvm_error(get_type_name(),
                  $sformatf("MISMATCH: %s <-> %s", mtx.convert2string(), stx.convert2string()))
               compare_fail++;
            end
         end

         // Check for unmatched transactions
         while (master_fifo.used() > 0) begin
            master_fifo.get(mtx);
            `uvm_warning(get_type_name(), $sformatf("Unmatched master: %s", mtx.convert2string()))
            master_only++;
         end
         while (slave_fifo.used() > 0) begin
            slave_fifo.get(stx);
            `uvm_warning(get_type_name(), $sformatf("Unmatched slave: %s", stx.convert2string()))
            slave_only++;
         end

         phase.drop_objection(this);
      endtask

      function void report_phase(uvm_phase phase);
         super.report_phase(phase);
         `uvm_info(get_type_name(), $sformatf("Scoreboard Results:"), UVM_LOW)
         `uvm_info(get_type_name(), $sformatf("  Pass: %0d", compare_pass), UVM_LOW)
         `uvm_info(get_type_name(), $sformatf("  Fail: %0d", compare_fail), UVM_LOW)
         `uvm_info(get_type_name(), $sformatf("  Master only: %0d", master_only), UVM_LOW)
         `uvm_info(get_type_name(), $sformatf("  Slave only: %0d", slave_only), UVM_LOW)
      endfunction
   endclass

   // Master monitor - publishes master transactions
   class master_monitor extends uvm_monitor;
      `uvm_component_utils(master_monitor)

      uvm_analysis_port #(master_tx) ap;

      function new(string name = "", uvm_component parent = null);
         super.new(name, parent);
      endfunction

      function void build_phase(uvm_phase phase);
         super.build_phase(phase);
         ap = new("ap", this);
      endfunction

      task publish(master_tx tx);
         `uvm_info(get_type_name(), $sformatf("Publishing: %s", tx.convert2string()), UVM_LOW)
         ap.write(tx);
      endtask
   endclass

   // Slave monitor - publishes slave transactions
   class slave_monitor extends uvm_monitor;
      `uvm_component_utils(slave_monitor)

      uvm_analysis_port #(slave_tx) ap;

      function new(string name = "", uvm_component parent = null);
         super.new(name, parent);
      endfunction

      function void build_phase(uvm_phase phase);
         super.build_phase(phase);
         ap = new("ap", this);
      endfunction

      task publish(slave_tx tx);
         `uvm_info(get_type_name(), $sformatf("Publishing: %s", tx.convert2string()), UVM_LOW)
         ap.write(tx);
      endtask
   endclass

   // Environment
   class my_env extends uvm_env;
      `uvm_component_utils(my_env)

      master_monitor m_mon;
      slave_monitor s_mon;
      dual_scoreboard scb;

      function new(string name = "", uvm_component parent = null);
         super.new(name, parent);
      endfunction

      function void build_phase(uvm_phase phase);
         super.build_phase(phase);
         m_mon = master_monitor::type_id::create("m_mon", this);
         s_mon = slave_monitor::type_id::create("s_mon", this);
         scb = dual_scoreboard::type_id::create("scb", this);
      endfunction

      function void connect_phase(uvm_phase phase);
         super.connect_phase(phase);
         // Connect master monitor to master FIFO
         m_mon.ap.connect(scb.master_fifo.analysis_export);
         // Connect slave monitor to slave FIFO
         s_mon.ap.connect(scb.slave_fifo.analysis_export);
         `uvm_info(get_type_name(), "Connected monitors to dual-FIFO scoreboard", UVM_LOW)
      endfunction
   endclass

   // Test
   class my_test extends uvm_test;
      `uvm_component_utils(my_test)

      my_env env;

      function new(string name = "", uvm_component parent = null);
         super.new(name, parent);
      endfunction

      function void build_phase(uvm_phase phase);
         super.build_phase(phase);
         env = my_env::type_id::create("env", this);
      endfunction

      task run_phase(uvm_phase phase);
         master_tx mtx;
         slave_tx stx;

         // Don't raise objection here - let scoreboard control it

         // Simulate bidirectional protocol transactions
         for (int i = 0; i < 4; i++) begin
            // Create matching master and slave transactions
            mtx = new($sformatf("mtx_%0d", i));
            mtx.addr = i;
            mtx.mosi_data = i * 10;

            stx = new($sformatf("stx_%0d", i));
            stx.addr = i;  // Matching address
            stx.miso_data = i * 20;

            // Publish both transactions
            env.m_mon.publish(mtx);
            env.s_mon.publish(stx);
         end
      endtask

      function void report_phase(uvm_phase phase);
         super.report_phase(phase);
         // Expected: 4 passes, 0 fails
         if (env.scb.compare_pass == 4 &&
             env.scb.compare_fail == 0 &&
             env.scb.master_only == 0 &&
             env.scb.slave_only == 0) begin
            $display("*-* All Finished *-*");
         end else begin
            `uvm_error(get_type_name(), "Test FAILED - unexpected scoreboard results")
         end
      endfunction
   endclass

   initial begin
      run_test("my_test");
   end

endmodule
