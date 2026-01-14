// DESCRIPTION: Verilator: Test transaction helper functions and post-randomize patterns
// This pattern is used in protocol verification (I3C, etc.) where transaction classes
// have helper functions to aggregate status across arrays and post_randomize modifies
// specific elements for protocol compliance
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define UVM_NO_DPI
`define UVM_REGEX_NO_DPI

module t;
   import uvm_pkg::*;
   `include "uvm_macros.svh"

   // Status enum (like I3C ACK/NACK)
   typedef enum bit {
      ACK  = 1'b0,
      NACK = 1'b1
   } status_e;

   // Operation enum
   typedef enum bit {
      WRITE = 1'b0,
      READ  = 1'b1
   } operation_e;

   // Transaction class with helper functions and post_randomize
   class protocol_tx extends uvm_sequence_item;
      `uvm_object_utils(protocol_tx)

      // Basic fields
      rand bit [6:0] target_address;
      rand operation_e operation;

      // Dynamic arrays for data and status (like I3C writeData/writeDataStatus)
      rand bit [7:0] write_data[];
      rand status_e write_status[];
      rand bit [7:0] read_data[];
      rand status_e read_status[];

      // Constraints
      constraint array_size_c {
         write_data.size() inside {[1:8]};
         write_status.size() == write_data.size();
         read_data.size() inside {[1:8]};
         read_status.size() == read_data.size();
      }

      // Operation-coupled constraints
      constraint operation_write_c {
         operation == WRITE -> write_data.size() > 0;
      }
      constraint operation_read_c {
         operation == READ -> read_data.size() > 0;
      }

      // Soft constraint for default status (can be overridden)
      constraint status_default_c {
         foreach (write_status[i]) soft write_status[i] == ACK;
         foreach (read_status[i]) soft read_status[i] == ACK;
      }

      function new(string name = "protocol_tx");
         super.new(name);
      endfunction

      // Post-randomize: Protocol requires last read_status to be NACK
      function void post_randomize();
         if (read_status.size() > 0) begin
            read_status[read_status.size()-1] = NACK;
         end
      endfunction

      // Helper function: Get aggregated write status
      // Returns {has_any_ack, has_any_nack}
      function bit [1:0] get_write_status_summary();
         bit has_ack = 0;
         bit has_nack = 0;
         foreach (write_status[i]) begin
            if (write_status[i] == ACK) has_ack = 1;
            else has_nack = 1;
         end
         return {has_ack, has_nack};
      endfunction

      // Helper function: Get aggregated read status
      function bit [1:0] get_read_status_summary();
         bit has_ack = 0;
         bit has_nack = 0;
         foreach (read_status[i]) begin
            if (read_status[i] == ACK) has_ack = 1;
            else has_nack = 1;
         end
         return {has_ack, has_nack};
      endfunction

      // Helper function: Count ACKs in write status
      function int count_write_acks();
         int count = 0;
         foreach (write_status[i]) begin
            if (write_status[i] == ACK) count++;
         end
         return count;
      endfunction

      // Helper function: Count ACKs in read status
      function int count_read_acks();
         int count = 0;
         foreach (read_status[i]) begin
            if (read_status[i] == ACK) count++;
         end
         return count;
      endfunction

      virtual function string convert2string();
         return $sformatf("addr=%h op=%s wr_size=%0d rd_size=%0d wr_status=%b rd_status=%b",
                          target_address, operation.name(), write_data.size(),
                          read_data.size(), get_write_status_summary(), get_read_status_summary());
      endfunction
   endclass

   // Test
   class my_test extends uvm_test;
      `uvm_component_utils(my_test)

      int test_count;
      int pass_count;

      function new(string name = "", uvm_component parent = null);
         super.new(name, parent);
         test_count = 0;
         pass_count = 0;
      endfunction

      task run_phase(uvm_phase phase);
         protocol_tx tx;
         bit [1:0] summary;
         int ack_count;

         phase.raise_objection(this);

         // Test 1: Post-randomize forces last read_status to NACK
         `uvm_info(get_type_name(), "Test 1: Post-randomize NACK enforcement", UVM_LOW)
         for (int i = 0; i < 5; i++) begin
            tx = new($sformatf("tx_%0d", i));
            void'(tx.randomize());
            test_count++;
            if (tx.read_status[tx.read_status.size()-1] == NACK) begin
               pass_count++;
               `uvm_info(get_type_name(), $sformatf("  PASS: Last read_status is NACK (size=%0d)",
                         tx.read_status.size()), UVM_LOW)
            end else begin
               `uvm_error(get_type_name(), "FAIL: Last read_status should be NACK")
            end
         end

         // Test 2: Helper function - get_write_status_summary
         `uvm_info(get_type_name(), "Test 2: Status summary helper function", UVM_LOW)
         tx = new("tx_summary");
         tx.write_data = new[4];
         tx.write_status = new[4];
         tx.write_status = '{ACK, ACK, NACK, ACK};  // Mixed
         tx.read_data = new[1];
         tx.read_status = new[1];
         tx.read_status = '{NACK};

         test_count++;
         summary = tx.get_write_status_summary();
         if (summary == 2'b11) begin  // has_ack=1, has_nack=1
            pass_count++;
            `uvm_info(get_type_name(), $sformatf("  PASS: Write summary=%b (mixed)", summary), UVM_LOW)
         end else begin
            `uvm_error(get_type_name(), $sformatf("FAIL: Expected 2'b11, got %b", summary))
         end

         // Test 3: Count ACKs helper function
         `uvm_info(get_type_name(), "Test 3: Count ACKs helper function", UVM_LOW)
         test_count++;
         ack_count = tx.count_write_acks();
         if (ack_count == 3) begin  // 3 ACKs in {ACK, ACK, NACK, ACK}
            pass_count++;
            `uvm_info(get_type_name(), $sformatf("  PASS: ACK count=%0d", ack_count), UVM_LOW)
         end else begin
            `uvm_error(get_type_name(), $sformatf("FAIL: Expected 3 ACKs, got %0d", ack_count))
         end

         // Test 4: All ACK summary
         `uvm_info(get_type_name(), "Test 4: All ACK summary", UVM_LOW)
         tx.write_status = '{ACK, ACK, ACK, ACK};
         test_count++;
         summary = tx.get_write_status_summary();
         if (summary == 2'b10) begin  // has_ack=1, has_nack=0
            pass_count++;
            `uvm_info(get_type_name(), $sformatf("  PASS: All ACK summary=%b", summary), UVM_LOW)
         end else begin
            `uvm_error(get_type_name(), $sformatf("FAIL: Expected 2'b10, got %b", summary))
         end

         // Test 5: All NACK summary
         `uvm_info(get_type_name(), "Test 5: All NACK summary", UVM_LOW)
         tx.write_status = '{NACK, NACK, NACK, NACK};
         test_count++;
         summary = tx.get_write_status_summary();
         if (summary == 2'b01) begin  // has_ack=0, has_nack=1
            pass_count++;
            `uvm_info(get_type_name(), $sformatf("  PASS: All NACK summary=%b", summary), UVM_LOW)
         end else begin
            `uvm_error(get_type_name(), $sformatf("FAIL: Expected 2'b01, got %b", summary))
         end

         #10;
         phase.drop_objection(this);
      endtask

      function void report_phase(uvm_phase phase);
         super.report_phase(phase);
         `uvm_info(get_type_name(), $sformatf("Results: %0d/%0d tests passed", pass_count, test_count), UVM_LOW)
         if (pass_count == test_count) begin
            $display("*-* All Finished *-*");
         end else begin
            `uvm_error(get_type_name(), "Some tests failed!")
         end
      endfunction
   endclass

   initial begin
      run_test("my_test");
   end

endmodule
