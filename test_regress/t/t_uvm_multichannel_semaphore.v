// DESCRIPTION: Verilator: Test multi-channel protocol coordination with semaphores
// This pattern is used in AVIPs like AXI4 where multiple channels (address, data, response)
// need to be synchronized using semaphores for proper handshaking
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define UVM_NO_DPI
`define UVM_REGEX_NO_DPI

module t;
   import uvm_pkg::*;
   `include "uvm_macros.svh"

   // Transaction class representing a write operation
   class write_tx extends uvm_sequence_item;
      `uvm_object_utils(write_tx)

      bit [7:0] addr;
      bit [31:0] data;
      bit [1:0] resp;  // 0=OKAY, 1=EXOKAY, 2=SLVERR, 3=DECERR

      function new(string name = "write_tx");
         super.new(name);
      endfunction

      virtual function string convert2string();
         return $sformatf("WRITE: addr=%h data=%h resp=%0d", addr, data, resp);
      endfunction
   endclass

   // Driver proxy with multi-channel coordination using semaphores
   // Models AXI4-like write: address channel -> data channel -> response channel
   class multichannel_driver extends uvm_component;
      `uvm_component_utils(multichannel_driver)

      // Semaphores for channel synchronization
      semaphore addr_channel_key;
      semaphore data_channel_key;
      semaphore resp_channel_key;

      // FIFOs for channel buffering
      uvm_tlm_analysis_fifo #(write_tx) addr_fifo;
      uvm_tlm_analysis_fifo #(write_tx) data_fifo;
      uvm_tlm_analysis_fifo #(write_tx) resp_fifo;

      // Analysis port for completed transactions
      uvm_analysis_port #(write_tx) completed_ap;

      // Statistics
      int addr_sent;
      int data_sent;
      int resp_received;

      function new(string name = "", uvm_component parent = null);
         super.new(name, parent);
         addr_channel_key = new(1);  // Binary semaphore
         data_channel_key = new(0);  // Blocked until addr phase completes
         resp_channel_key = new(0);  // Blocked until data phase completes
         addr_sent = 0;
         data_sent = 0;
         resp_received = 0;
      endfunction

      function void build_phase(uvm_phase phase);
         super.build_phase(phase);
         addr_fifo = new("addr_fifo", this);
         data_fifo = new("data_fifo", this);
         resp_fifo = new("resp_fifo", this);
         completed_ap = new("completed_ap", this);
      endfunction

      // Submit a transaction - goes through all 3 channels
      task submit_write(write_tx tx);
         write_tx addr_tx, data_tx, resp_tx;

         // Clone for each channel
         addr_tx = new("addr_phase");
         addr_tx.addr = tx.addr;
         data_tx = new("data_phase");
         data_tx.data = tx.data;
         resp_tx = new("resp_phase");

         // Fork all channels to run concurrently
         fork
            // Address channel
            begin
               addr_channel_key.get(1);  // Wait for turn
               `uvm_info(get_type_name(), $sformatf("ADDR phase: addr=%h", addr_tx.addr), UVM_LOW)
               addr_fifo.write(addr_tx);
               addr_sent++;
               #5;  // Simulate address handshake
               data_channel_key.put(1);  // Signal data can proceed
            end

            // Data channel
            begin
               data_channel_key.get(1);  // Wait for address to complete
               `uvm_info(get_type_name(), $sformatf("DATA phase: data=%h", data_tx.data), UVM_LOW)
               data_fifo.write(data_tx);
               data_sent++;
               #5;  // Simulate data transfer
               resp_channel_key.put(1);  // Signal response can proceed
            end

            // Response channel
            begin
               resp_channel_key.get(1);  // Wait for data to complete
               resp_tx.resp = 0;  // OKAY
               `uvm_info(get_type_name(), $sformatf("RESP phase: resp=%0d", resp_tx.resp), UVM_LOW)
               resp_fifo.write(resp_tx);
               resp_received++;
               #5;  // Simulate response
               addr_channel_key.put(1);  // Release for next transaction
            end
         join

         // Merge into completed transaction
         tx.resp = resp_tx.resp;
         completed_ap.write(tx);
      endtask

      function void report_phase(uvm_phase phase);
         super.report_phase(phase);
         `uvm_info(get_type_name(), $sformatf("Driver Stats: addr=%0d data=%0d resp=%0d",
                                              addr_sent, data_sent, resp_received), UVM_LOW)
      endfunction
   endclass

   // Subscriber to collect completed transactions
   class tx_collector extends uvm_subscriber #(write_tx);
      `uvm_component_utils(tx_collector)

      write_tx collected[$];

      function new(string name = "", uvm_component parent = null);
         super.new(name, parent);
      endfunction

      virtual function void write(write_tx t);
         `uvm_info(get_type_name(), $sformatf("Collected: %s", t.convert2string()), UVM_LOW)
         collected.push_back(t);
      endfunction

      function int get_count();
         return collected.size();
      endfunction
   endclass

   // Test
   class my_test extends uvm_test;
      `uvm_component_utils(my_test)

      multichannel_driver drv;
      tx_collector collector;

      function new(string name = "", uvm_component parent = null);
         super.new(name, parent);
      endfunction

      function void build_phase(uvm_phase phase);
         super.build_phase(phase);
         drv = multichannel_driver::type_id::create("drv", this);
         collector = tx_collector::type_id::create("collector", this);
      endfunction

      function void connect_phase(uvm_phase phase);
         super.connect_phase(phase);
         drv.completed_ap.connect(collector.analysis_export);
      endfunction

      task run_phase(uvm_phase phase);
         write_tx tx;

         phase.raise_objection(this);

         // Submit 4 transactions sequentially
         for (int i = 0; i < 4; i++) begin
            tx = new($sformatf("tx_%0d", i));
            tx.addr = i * 16;
            tx.data = i * 256;
            drv.submit_write(tx);
         end

         #10;  // Allow completion

         phase.drop_objection(this);
      endtask

      function void report_phase(uvm_phase phase);
         super.report_phase(phase);
         // Verify all transactions completed through all channels
         if (drv.addr_sent == 4 &&
             drv.data_sent == 4 &&
             drv.resp_received == 4 &&
             collector.get_count() == 4) begin
            $display("*-* All Finished *-*");
         end else begin
            `uvm_error(get_type_name(), $sformatf("Mismatch: addr=%0d data=%0d resp=%0d collected=%0d",
                       drv.addr_sent, drv.data_sent, drv.resp_received, collector.get_count()))
         end
      endfunction
   endclass

   initial begin
      run_test("my_test");
   end

endmodule
