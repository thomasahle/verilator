// DESCRIPTION: Verilator: Test dynamic arrays of parameterized TLM FIFOs
// This pattern is used in AVIP scoreboards to handle multiple agents
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define UVM_NO_DPI
`define UVM_REGEX_NO_DPI

module t;
   import uvm_pkg::*;
   `include "uvm_macros.svh"

   // Transaction class
   class my_tx extends uvm_sequence_item;
      `uvm_object_utils(my_tx)

      int id;
      int data;

      function new(string name = "my_tx");
         super.new(name);
      endfunction

      virtual function string convert2string();
         return $sformatf("id=%0d data=%0d", id, data);
      endfunction
   endclass

   // Producer - sends to analysis port
   class producer extends uvm_component;
      `uvm_component_utils(producer)

      uvm_analysis_port #(my_tx) ap;
      int producer_id;

      function new(string name = "producer", uvm_component parent = null);
         super.new(name, parent);
      endfunction

      function void build_phase(uvm_phase phase);
         super.build_phase(phase);
         ap = new("ap", this);
      endfunction

      task send(int count);
         for (int i = 0; i < count; i++) begin
            my_tx tx = my_tx::type_id::create($sformatf("tx_%0d", i));
            tx.id = producer_id;
            tx.data = i * 10 + producer_id;
            `uvm_info(get_type_name(), $sformatf("Producer %0d sending: %s", producer_id, tx.convert2string()), UVM_LOW)
            ap.write(tx);
         end
      endtask
   endclass

   // Scoreboard with dynamic array of TLM FIFOs - pattern from AVIP
   class scoreboard extends uvm_component;
      `uvm_component_utils(scoreboard)

      // Dynamic array of parameterized TLM FIFOs
      uvm_tlm_analysis_fifo #(my_tx) fifo_array[];
      int num_fifos;
      int total_received;

      function new(string name = "scoreboard", uvm_component parent = null);
         super.new(name, parent);
         total_received = 0;
      endfunction

      function void build_phase(uvm_phase phase);
         super.build_phase(phase);
         // Allocate array based on config
         fifo_array = new[num_fifos];
         // Initialize each FIFO with unique name
         foreach (fifo_array[i]) begin
            fifo_array[i] = new($sformatf("fifo_array[%0d]", i), this);
         end
         `uvm_info(get_type_name(), $sformatf("Created %0d analysis FIFOs", num_fifos), UVM_LOW)
      endfunction

      task check_all();
         my_tx tx;
         // Read from all FIFOs
         foreach (fifo_array[i]) begin
            while (fifo_array[i].try_get(tx)) begin
               total_received++;
               `uvm_info(get_type_name(), $sformatf("FIFO[%0d] got: %s", i, tx.convert2string()), UVM_LOW)
            end
         end
      endtask

      function void report_phase(uvm_phase phase);
         super.report_phase(phase);
         `uvm_info(get_type_name(), $sformatf("Total received across all FIFOs: %0d", total_received), UVM_LOW)
      endfunction
   endclass

   // Environment
   class my_env extends uvm_env;
      `uvm_component_utils(my_env)

      localparam int NUM_PRODUCERS = 3;
      producer producers[NUM_PRODUCERS];
      scoreboard scb;

      function new(string name = "my_env", uvm_component parent = null);
         super.new(name, parent);
      endfunction

      function void build_phase(uvm_phase phase);
         super.build_phase(phase);
         // Set scoreboard config before create
         scb = scoreboard::type_id::create("scb", this);
         scb.num_fifos = NUM_PRODUCERS;
         // Create producers
         foreach (producers[i]) begin
            producers[i] = producer::type_id::create($sformatf("producer_%0d", i), this);
            producers[i].producer_id = i;
         end
      endfunction

      function void connect_phase(uvm_phase phase);
         super.connect_phase(phase);
         // Connect each producer to corresponding FIFO
         foreach (producers[i]) begin
            producers[i].ap.connect(scb.fifo_array[i].analysis_export);
            `uvm_info(get_type_name(), $sformatf("Connected producer[%0d] to fifo_array[%0d]", i, i), UVM_LOW)
         end
      endfunction
   endclass

   // Test
   class my_test extends uvm_test;
      `uvm_component_utils(my_test)

      my_env env;

      function new(string name = "my_test", uvm_component parent = null);
         super.new(name, parent);
      endfunction

      function void build_phase(uvm_phase phase);
         super.build_phase(phase);
         env = my_env::type_id::create("env", this);
      endfunction

      task run_phase(uvm_phase phase);
         phase.raise_objection(this);

         // Each producer sends 2 transactions
         foreach (env.producers[i]) begin
            env.producers[i].send(2);
         end

         #10;

         // Check all FIFOs
         env.scb.check_all();

         phase.drop_objection(this);
      endtask

      function void report_phase(uvm_phase phase);
         super.report_phase(phase);
         // Expected: 3 producers * 2 transactions = 6 total
         if (env.scb.total_received == 6) begin
            $display("*-* All Finished *-*");
         end else begin
            `uvm_error(get_type_name(), $sformatf("Expected 6 transactions, got %0d", env.scb.total_received))
         end
      endfunction
   endclass

   initial begin
      run_test("my_test");
   end

endmodule
