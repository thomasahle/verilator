// DESCRIPTION: Verilator: Verilog Test module for UVM analysis port
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define UVM_NO_DPI
`define UVM_REGEX_NO_DPI

module t;
   import uvm_pkg::*;
   `include "uvm_macros.svh"

   // Simple transaction class
   class my_transaction extends uvm_sequence_item;
      `uvm_object_utils(my_transaction)

      int data;
      int addr;

      function new(string name = "my_transaction");
         super.new(name);
      endfunction

      virtual function string convert2string();
         return $sformatf("addr=%0h data=%0h", addr, data);
      endfunction
   endclass

   // Producer component - writes to analysis port
   class my_producer extends uvm_component;
      `uvm_component_utils(my_producer)

      uvm_analysis_port #(my_transaction) analysis_port;
      int num_sent = 0;

      function new(string name = "my_producer", uvm_component parent = null);
         super.new(name, parent);
      endfunction

      function void build_phase(uvm_phase phase);
         super.build_phase(phase);
         analysis_port = new("analysis_port", this);
      endfunction

      task run_phase(uvm_phase phase);
         my_transaction tx;
         phase.raise_objection(this);

         // Send 5 transactions
         for (int i = 0; i < 5; i++) begin
            tx = my_transaction::type_id::create($sformatf("tx_%0d", i));
            tx.addr = i * 4;
            tx.data = i * 100;
            `uvm_info(get_type_name(), $sformatf("Sending: %s", tx.convert2string()), UVM_LOW)
            analysis_port.write(tx);
            num_sent++;
            #10;
         end

         phase.drop_objection(this);
      endtask

      function void report_phase(uvm_phase phase);
         super.report_phase(phase);
         `uvm_info(get_type_name(), $sformatf("Producer sent %0d transactions", num_sent), UVM_LOW)
      endfunction
   endclass

   // Consumer using subscriber pattern
   class my_subscriber extends uvm_subscriber #(my_transaction);
      `uvm_component_utils(my_subscriber)

      int num_received = 0;
      my_transaction received_txs[$];

      function new(string name = "my_subscriber", uvm_component parent = null);
         super.new(name, parent);
      endfunction

      function void write(my_transaction t);
         `uvm_info(get_type_name(), $sformatf("Received: %s", t.convert2string()), UVM_LOW)
         received_txs.push_back(t);
         num_received++;
      endfunction

      function void report_phase(uvm_phase phase);
         super.report_phase(phase);
         `uvm_info(get_type_name(), $sformatf("Subscriber received %0d transactions", num_received), UVM_LOW)
      endfunction
   endclass

   // Consumer using analysis_fifo
   class my_fifo_consumer extends uvm_component;
      `uvm_component_utils(my_fifo_consumer)

      uvm_tlm_analysis_fifo #(my_transaction) analysis_fifo;
      int num_received = 0;

      function new(string name = "my_fifo_consumer", uvm_component parent = null);
         super.new(name, parent);
      endfunction

      function void build_phase(uvm_phase phase);
         super.build_phase(phase);
         analysis_fifo = new("analysis_fifo", this);
      endfunction

      task run_phase(uvm_phase phase);
         my_transaction tx;
         phase.raise_objection(this);

         // Give producer time to send
         #5;

         // Read from FIFO until empty
         while (1) begin
            if (analysis_fifo.try_get(tx)) begin
               `uvm_info(get_type_name(), $sformatf("FIFO got: %s", tx.convert2string()), UVM_LOW)
               num_received++;
            end
            else begin
               // Nothing in fifo, wait or break
               #10;
               if (!analysis_fifo.try_get(tx))
                  break;  // Still empty, we're done
               else begin
                  `uvm_info(get_type_name(), $sformatf("FIFO got: %s", tx.convert2string()), UVM_LOW)
                  num_received++;
               end
            end
         end

         phase.drop_objection(this);
      endtask

      function void report_phase(uvm_phase phase);
         super.report_phase(phase);
         `uvm_info(get_type_name(), $sformatf("FIFO consumer received %0d transactions", num_received), UVM_LOW)
      endfunction
   endclass

   // Environment that wires everything together
   class my_env extends uvm_env;
      `uvm_component_utils(my_env)

      my_producer producer;
      my_subscriber subscriber;
      my_fifo_consumer fifo_consumer;

      function new(string name = "my_env", uvm_component parent = null);
         super.new(name, parent);
      endfunction

      function void build_phase(uvm_phase phase);
         super.build_phase(phase);
         producer = my_producer::type_id::create("producer", this);
         subscriber = my_subscriber::type_id::create("subscriber", this);
         fifo_consumer = my_fifo_consumer::type_id::create("fifo_consumer", this);
      endfunction

      function void connect_phase(uvm_phase phase);
         super.connect_phase(phase);
         // Connect producer's analysis port to both consumers
         producer.analysis_port.connect(subscriber.analysis_export);
         producer.analysis_port.connect(fifo_consumer.analysis_fifo.analysis_export);
      endfunction

      function void report_phase(uvm_phase phase);
         super.report_phase(phase);
         // Verify counts
         if (producer.num_sent != 5)
            `uvm_error(get_type_name(), $sformatf("Producer sent wrong count: %0d != 5", producer.num_sent))
         if (subscriber.num_received != 5)
            `uvm_error(get_type_name(), $sformatf("Subscriber received wrong count: %0d != 5", subscriber.num_received))
         if (fifo_consumer.num_received != 5)
            `uvm_error(get_type_name(), $sformatf("FIFO consumer received wrong count: %0d != 5", fifo_consumer.num_received))

         // Verify subscriber received correct data
         for (int i = 0; i < 5; i++) begin
            my_transaction tx = subscriber.received_txs[i];
            if (tx.addr != i * 4)
               `uvm_error(get_type_name(), $sformatf("Transaction %0d addr mismatch: %0h != %0h", i, tx.addr, i*4))
            if (tx.data != i * 100)
               `uvm_error(get_type_name(), $sformatf("Transaction %0d data mismatch: %0h != %0h", i, tx.data, i*100))
         end
      endfunction
   endclass

   // Test class
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

      function void report_phase(uvm_phase phase);
         super.report_phase(phase);
         if (uvm_report_server::get_server().get_severity_count(UVM_ERROR) == 0)
            $display("*-* All Finished *-*");
         else
            `uvm_fatal(get_type_name(), "Test FAILED due to errors")
      endfunction
   endclass

   initial begin
      run_test("my_test");
   end

endmodule
