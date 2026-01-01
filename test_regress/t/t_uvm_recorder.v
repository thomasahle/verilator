// DESCRIPTION: Verilator: Verilog Test module
//
// Test uvm_recorder for transaction recording
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`include "uvm_macros.svh"

module t;
   import uvm_pkg::*;

   // Custom object for testing recording
   class RecordableObject extends uvm_object;
      `uvm_object_utils(RecordableObject)

      bit [31:0] addr;
      bit [7:0] data;
      string name_str;

      function new(string name = "RecordableObject");
         super.new(name);
      endfunction

      virtual function void do_record(uvm_recorder recorder);
         super.do_record(recorder);
         recorder.record_field("addr", addr, 32, UVM_HEX);
         recorder.record_field("data", data, 8, UVM_HEX);
         recorder.record_string("name_str", name_str);
      endfunction
   endclass

   // Nested object for testing recursive recording
   class ContainerObject extends uvm_object;
      `uvm_object_utils(ContainerObject)

      bit [15:0] id;
      RecordableObject inner;

      function new(string name = "ContainerObject");
         super.new(name);
         inner = new("inner");
      endfunction

      virtual function void do_record(uvm_recorder recorder);
         super.do_record(recorder);
         recorder.record_field("id", id, 16, UVM_DEC);
         recorder.record_object("inner", inner);
      endfunction
   endclass

   // Test component
   class test extends uvm_test;
      `uvm_component_utils(test)

      function new(string name, uvm_component parent);
         super.new(name, parent);
      endfunction

      task run_phase(uvm_phase phase);
         RecordableObject obj;
         ContainerObject container;
         uvm_recorder recorder;
         string fields[$];
         bit passed = 1;

         phase.raise_objection(this);

         // Create test objects
         obj = RecordableObject::type_id::create("obj");
         obj.addr = 32'hCAFEBABE;
         obj.data = 8'h42;
         obj.name_str = "hello";

         container = ContainerObject::type_id::create("container");
         container.id = 16'd1234;
         container.inner.addr = 32'h12345678;
         container.inner.data = 8'hFF;
         container.inner.name_str = "world";

         // Test 1: Create and open recorder
         recorder = new("test_recorder");
         recorder.open_file("test.log");

         if (recorder.is_open()) begin
            `uvm_info("TEST", "PASS: recorder is open", UVM_LOW)
         end else begin
            `uvm_error("TEST", "FAIL: recorder not open")
            passed = 0;
         end

         // Test 2: Set scope and record simple object
         recorder.set_scope("simple_obj");
         obj.do_record(recorder);

         // Check recorded fields
         recorder.get_fields(fields);
         `uvm_info("TEST", $sformatf("Recorded %0d fields", fields.size()), UVM_LOW)

         if (fields.size() == 3) begin
            `uvm_info("TEST", "PASS: correct number of fields recorded", UVM_LOW)
         end else begin
            `uvm_error("TEST", $sformatf("FAIL: expected 3 fields, got %0d", fields.size()))
            passed = 0;
         end

         // Print recorded fields
         foreach (fields[i]) begin
            `uvm_info("TEST", {"  Field: ", fields[i]}, UVM_LOW)
         end

         // Test 3: Clear and record container with nested object
         recorder.clear();
         recorder.set_scope("container_obj");
         container.do_record(recorder);

         recorder.get_fields(fields);
         `uvm_info("TEST", $sformatf("Container recorded %0d fields", fields.size()), UVM_LOW)

         // Container should have: id, inner.addr, inner.data, inner.name_str = 4 fields
         if (fields.size() == 4) begin
            `uvm_info("TEST", "PASS: nested object recording works", UVM_LOW)
         end else begin
            `uvm_error("TEST", $sformatf("FAIL: expected 4 fields for container, got %0d", fields.size()))
            passed = 0;
         end

         foreach (fields[i]) begin
            `uvm_info("TEST", {"  Field: ", fields[i]}, UVM_LOW)
         end

         // Test 4: Close recorder
         recorder.close();
         if (!recorder.is_open()) begin
            `uvm_info("TEST", "PASS: recorder closed", UVM_LOW)
         end else begin
            `uvm_error("TEST", "FAIL: recorder still open")
            passed = 0;
         end

         // Test 5: Test recording with different radix
         recorder.clear();
         recorder.set_scope("radix_test");
         recorder.record_field("bin_val", 8'b10101010, 8, UVM_BIN);
         recorder.record_field("dec_val", 32'd12345, 32, UVM_DEC);
         recorder.record_field("hex_val", 32'hABCD, 32, UVM_HEX);

         recorder.get_fields(fields);
         if (fields.size() == 3) begin
            `uvm_info("TEST", "PASS: radix recording works", UVM_LOW)
         end else begin
            `uvm_error("TEST", "FAIL: radix recording issue")
            passed = 0;
         end

         foreach (fields[i]) begin
            `uvm_info("TEST", {"  Field: ", fields[i]}, UVM_LOW)
         end

         if (passed) begin
            `uvm_info("TEST", "All recorder tests passed!", UVM_LOW)
         end

         $write("*-* All Finished *-*\n");
         $finish;
      endtask
   endclass

   initial begin
      run_test("test");
   end
endmodule
