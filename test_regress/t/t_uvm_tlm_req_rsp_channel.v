// DESCRIPTION: Verilator: Test UVM TLM request/response channel functionality
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test uvm_tlm_req_rsp_channel

`include "uvm_macros.svh"

module t;
  import uvm_pkg::*;

  // Request transaction
  class request_tx extends uvm_object;
    `uvm_object_utils(request_tx)
    int req_id;
    int data;

    function new(string name = "request_tx");
      super.new(name);
    endfunction
  endclass

  // Response transaction
  class response_tx extends uvm_object;
    `uvm_object_utils(response_tx)
    int req_id;
    int result;

    function new(string name = "response_tx");
      super.new(name);
    endfunction
  endclass

  // Initiator component - sends requests and gets responses
  class initiator extends uvm_component;
    `uvm_component_utils(initiator)
    uvm_tlm_req_rsp_channel #(request_tx, response_tx) channel;
    int responses_received;

    function new(string name, uvm_component parent);
      super.new(name, parent);
      responses_received = 0;
    endfunction

    task send_request(int id, int data);
      request_tx req = new("req");
      req.req_id = id;
      req.data = data;
      `uvm_info("INITIATOR", $sformatf("Sending request id=%0d, data=%0d", id, data), UVM_MEDIUM)
      channel.put_request(req);
    endtask

    task get_response(output int id, output int result);
      response_tx rsp;
      channel.get_response(rsp);
      id = rsp.req_id;
      result = rsp.result;
      responses_received++;
      `uvm_info("INITIATOR", $sformatf("Got response id=%0d, result=%0d", id, result), UVM_MEDIUM)
    endtask
  endclass

  // Target component - processes requests and sends responses
  class target extends uvm_component;
    `uvm_component_utils(target)
    uvm_tlm_req_rsp_channel #(request_tx, response_tx) channel;
    int requests_processed;

    function new(string name, uvm_component parent);
      super.new(name, parent);
      requests_processed = 0;
    endfunction

    task process();
      request_tx req;
      response_tx rsp;

      channel.get_request(req);
      requests_processed++;
      `uvm_info("TARGET", $sformatf("Processing request id=%0d, data=%0d", req.req_id, req.data), UVM_MEDIUM)

      // Simulate processing - result is data * 2
      rsp = new("rsp");
      rsp.req_id = req.req_id;
      rsp.result = req.data * 2;

      #5;  // Simulate processing delay
      channel.put_response(rsp);
      `uvm_info("TARGET", $sformatf("Sent response id=%0d, result=%0d", rsp.req_id, rsp.result), UVM_MEDIUM)
    endtask
  endclass

  // Test
  class test extends uvm_test;
    `uvm_component_utils(test)

    initiator init;
    target tgt;
    uvm_tlm_req_rsp_channel #(request_tx, response_tx) channel;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      init = initiator::type_id::create("init", this);
      tgt = target::type_id::create("tgt", this);
      channel = new("channel", this, 4, 4);  // 4-deep request and response FIFOs
    endfunction

    virtual function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      // Both initiator and target share the same channel
      init.channel = channel;
      tgt.channel = channel;
    endfunction

    virtual task run_phase(uvm_phase phase);
      int id, result;

      phase.raise_objection(this);

      `uvm_info("TEST", "Testing req/rsp channel", UVM_LOW)

      // Initial state checks
      if (!channel.request_is_empty()) begin
        `uvm_error("TEST", "Request FIFO should be empty initially")
      end
      if (!channel.response_is_empty()) begin
        `uvm_error("TEST", "Response FIFO should be empty initially")
      end

      // Start target processing in background
      fork
        begin
          repeat (3) tgt.process();
        end
      join_none

      // Send 3 requests
      init.send_request(1, 10);
      init.send_request(2, 20);
      init.send_request(3, 30);

      // Check request FIFO usage
      `uvm_info("TEST", $sformatf("Requests in FIFO: %0d", channel.request_used()), UVM_MEDIUM)

      // Wait for and check responses
      init.get_response(id, result);
      if (id != 1 || result != 20) begin
        `uvm_error("TEST", $sformatf("Response 1 mismatch: id=%0d, result=%0d", id, result))
      end

      init.get_response(id, result);
      if (id != 2 || result != 40) begin
        `uvm_error("TEST", $sformatf("Response 2 mismatch: id=%0d, result=%0d", id, result))
      end

      init.get_response(id, result);
      if (id != 3 || result != 60) begin
        `uvm_error("TEST", $sformatf("Response 3 mismatch: id=%0d, result=%0d", id, result))
      end

      #10;

      // Verify counts
      if (tgt.requests_processed != 3) begin
        `uvm_error("TEST", $sformatf("Expected 3 requests processed, got %0d", tgt.requests_processed))
      end
      if (init.responses_received != 3) begin
        `uvm_error("TEST", $sformatf("Expected 3 responses received, got %0d", init.responses_received))
      end

      // Test flush
      channel.flush();
      if (!channel.request_is_empty() || !channel.response_is_empty()) begin
        `uvm_error("TEST", "FIFOs should be empty after flush")
      end

      `uvm_info("TEST", "All req/rsp channel tests PASSED", UVM_LOW)

      phase.drop_objection(this);
    endtask

    virtual function void report_phase(uvm_phase phase);
      super.report_phase(phase);
      $write("*-* All Finished *-*\n");
    endfunction
  endclass

  initial begin
    run_test("test");
  end
endmodule
