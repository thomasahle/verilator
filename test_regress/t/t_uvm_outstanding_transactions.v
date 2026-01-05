// DESCRIPTION: Verilator: Test outstanding transactions pattern
// This pattern is used in high-performance protocols like AXI4 where multiple
// transactions can be in-flight simultaneously and may complete out of order
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define UVM_NO_DPI
`define UVM_REGEX_NO_DPI

module t;
   import uvm_pkg::*;
   `include "uvm_macros.svh"

   // Transaction with ID for tracking
   class tagged_tx extends uvm_sequence_item;
      `uvm_object_utils(tagged_tx)

      bit [3:0] id;          // Transaction ID
      bit [7:0] addr;
      bit [31:0] data;
      int latency;           // Simulated response latency

      function new(string name = "tagged_tx");
         super.new(name);
      endfunction

      virtual function string convert2string();
         return $sformatf("ID=%0d addr=%h data=%h latency=%0d", id, addr, data, latency);
      endfunction
   endclass

   // Response transaction
   class resp_tx extends uvm_sequence_item;
      `uvm_object_utils(resp_tx)

      bit [3:0] id;
      bit [1:0] resp;

      function new(string name = "resp_tx");
         super.new(name);
      endfunction

      virtual function string convert2string();
         return $sformatf("RESP ID=%0d status=%0d", id, resp);
      endfunction
   endclass

   // Outstanding transaction manager
   // Supports multiple concurrent transactions completing out of order
   class outstanding_manager extends uvm_component;
      `uvm_component_utils(outstanding_manager)

      // Track pending transactions by ID
      tagged_tx pending[16];  // Fixed array indexed by ID
      int pending_count;

      // Analysis ports
      uvm_analysis_port #(tagged_tx) request_ap;
      uvm_analysis_port #(resp_tx) response_ap;

      // Completion order tracking
      int completion_order[$];

      function new(string name = "", uvm_component parent = null);
         super.new(name, parent);
         pending_count = 0;
         foreach (pending[i]) pending[i] = null;
      endfunction

      function void build_phase(uvm_phase phase);
         super.build_phase(phase);
         request_ap = new("request_ap", this);
         response_ap = new("response_ap", this);
      endfunction

      // Submit a new transaction (non-blocking)
      task submit(tagged_tx tx);
         if (pending[tx.id] != null) begin
            `uvm_error(get_type_name(), $sformatf("ID %0d already in flight!", tx.id))
            return;
         end

         pending[tx.id] = tx;
         pending_count++;
         `uvm_info(get_type_name(), $sformatf("Submitted: %s (outstanding=%0d)",
                                              tx.convert2string(), pending_count), UVM_LOW)
         request_ap.write(tx);

         // Fork the response handler - each runs independently
         fork
            handle_response(tx);
         join_none
      endtask

      // Handle response after latency (runs concurrently for each transaction)
      task handle_response(tagged_tx tx);
         resp_tx resp;

         // Wait for specified latency (simulates varying response times)
         #(tx.latency);

         // Create response
         resp = new($sformatf("resp_%0d", tx.id));
         resp.id = tx.id;
         resp.resp = 0;  // OKAY

         // Complete the transaction
         pending[tx.id] = null;
         pending_count--;
         completion_order.push_back(tx.id);

         `uvm_info(get_type_name(), $sformatf("Completed: ID=%0d (outstanding=%0d)",
                                              tx.id, pending_count), UVM_LOW)
         response_ap.write(resp);
      endtask

      function int get_outstanding_count();
         return pending_count;
      endfunction

      function void get_completion_order(output int order[$]);
         order = completion_order;
      endfunction

      function void report_phase(uvm_phase phase);
         string order_str;
         super.report_phase(phase);
         order_str = "";
         foreach (completion_order[i]) begin
            order_str = {order_str, $sformatf("%0d ", completion_order[i])};
         end
         `uvm_info(get_type_name(), $sformatf("Completion order: %s", order_str), UVM_LOW)
      endfunction
   endclass

   // Request collector
   class request_collector extends uvm_subscriber #(tagged_tx);
      `uvm_component_utils(request_collector)

      int count;

      function new(string name = "", uvm_component parent = null);
         super.new(name, parent);
         count = 0;
      endfunction

      virtual function void write(tagged_tx t);
         count++;
      endfunction
   endclass

   // Response collector
   class response_collector extends uvm_subscriber #(resp_tx);
      `uvm_component_utils(response_collector)

      int count;
      int ids[$];

      function new(string name = "", uvm_component parent = null);
         super.new(name, parent);
         count = 0;
      endfunction

      virtual function void write(resp_tx t);
         count++;
         ids.push_back(t.id);
      endfunction
   endclass

   // Test
   class my_test extends uvm_test;
      `uvm_component_utils(my_test)

      outstanding_manager mgr;
      request_collector req_col;
      response_collector resp_col;

      function new(string name = "", uvm_component parent = null);
         super.new(name, parent);
      endfunction

      function void build_phase(uvm_phase phase);
         super.build_phase(phase);
         mgr = outstanding_manager::type_id::create("mgr", this);
         req_col = request_collector::type_id::create("req_col", this);
         resp_col = response_collector::type_id::create("resp_col", this);
      endfunction

      function void connect_phase(uvm_phase phase);
         super.connect_phase(phase);
         mgr.request_ap.connect(req_col.analysis_export);
         mgr.response_ap.connect(resp_col.analysis_export);
      endfunction

      task run_phase(uvm_phase phase);
         tagged_tx tx;

         phase.raise_objection(this);

         // Submit 4 transactions with different latencies
         // They should complete out of order based on latency
         tx = new("tx_0"); tx.id = 0; tx.addr = 'h00; tx.data = 100; tx.latency = 30;
         mgr.submit(tx);

         tx = new("tx_1"); tx.id = 1; tx.addr = 'h10; tx.data = 200; tx.latency = 10;  // Fast
         mgr.submit(tx);

         tx = new("tx_2"); tx.id = 2; tx.addr = 'h20; tx.data = 300; tx.latency = 20;
         mgr.submit(tx);

         tx = new("tx_3"); tx.id = 3; tx.addr = 'h30; tx.data = 400; tx.latency = 5;   // Fastest
         mgr.submit(tx);

         // Wait for all to complete
         wait(mgr.get_outstanding_count() == 0);
         #10;

         phase.drop_objection(this);
      endtask

      function void report_phase(uvm_phase phase);
         int order[$];
         super.report_phase(phase);

         // Verify all transactions sent and received
         if (req_col.count != 4) begin
            `uvm_error(get_type_name(), $sformatf("Expected 4 requests, got %0d", req_col.count))
            return;
         end
         if (resp_col.count != 4) begin
            `uvm_error(get_type_name(), $sformatf("Expected 4 responses, got %0d", resp_col.count))
            return;
         end

         // Verify out-of-order completion (ID 3 should complete first, then 1, 2, 0)
         mgr.get_completion_order(order);
         if (order[0] == 3 && order[1] == 1 && order[2] == 2 && order[3] == 0) begin
            `uvm_info(get_type_name(), "Out-of-order completion verified!", UVM_LOW)
            $display("*-* All Finished *-*");
         end else begin
            `uvm_error(get_type_name(), $sformatf("Unexpected completion order"))
         end
      endfunction
   endclass

   initial begin
      run_test("my_test");
   end

endmodule
