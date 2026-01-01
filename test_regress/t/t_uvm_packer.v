// DESCRIPTION: Verilator: Verilog Test module
//
// Test uvm_packer for packing/unpacking objects to bit streams
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`include "uvm_macros.svh"

module t;
   import uvm_pkg::*;

   // Custom object for testing packing
   class PackableObject extends uvm_object;
      `uvm_object_utils(PackableObject)

      bit [31:0] addr;
      bit [7:0] data;
      bit [3:0] len;
      string name_str;

      function new(string name = "PackableObject");
         super.new(name);
      endfunction

      virtual function void do_pack(uvm_packer packer);
         super.do_pack(packer);
         packer.pack_field_int(addr, 32);
         packer.pack_field_int(data, 8);
         packer.pack_field_int(len, 4);
         packer.pack_string(name_str);
      endfunction

      virtual function void do_unpack(uvm_packer packer);
         super.do_unpack(packer);
         addr = packer.unpack_field_int(32);
         data = packer.unpack_field_int(8);
         len = packer.unpack_field_int(4);
         name_str = packer.unpack_string();
      endfunction

      virtual function string convert2string();
         return $sformatf("addr=0x%08x, data=0x%02x, len=%0d, name=%s", addr, data, len, name_str);
      endfunction
   endclass

   // Test component
   class test extends uvm_test;
      `uvm_component_utils(test)

      function new(string name, uvm_component parent);
         super.new(name, parent);
      endfunction

      task run_phase(uvm_phase phase);
         PackableObject obj1, obj2;
         uvm_packer packer;
         int bit_count;
         bit passed = 1;

         phase.raise_objection(this);

         // Create test object with known values
         obj1 = PackableObject::type_id::create("obj1");
         obj1.addr = 32'hDEADBEEF;
         obj1.data = 8'hAB;
         obj1.len = 4'd7;
         obj1.name_str = "test123";

         `uvm_info("TEST", {"Original: ", obj1.convert2string()}, UVM_LOW)

         // Test 1: Pack object
         packer = new("packer");
         obj1.pack(packer);
         bit_count = packer.get_packed_size();
         `uvm_info("TEST", $sformatf("Packed %0d bits", bit_count), UVM_LOW)

         if (bit_count > 0) begin
            `uvm_info("TEST", "PASS: pack() produced output", UVM_LOW)
         end else begin
            `uvm_error("TEST", "FAIL: pack() produced no output")
            passed = 0;
         end

         // Test 2: Reset unpack position and unpack
         packer.set_packed_size();  // Reset for unpacking
         obj2 = PackableObject::type_id::create("obj2");
         obj2.unpack(packer);

         `uvm_info("TEST", {"Unpacked: ", obj2.convert2string()}, UVM_LOW)

         // Test 3: Verify field values
         if (obj2.addr == 32'hDEADBEEF) begin
            `uvm_info("TEST", "PASS: addr matches", UVM_LOW)
         end else begin
            `uvm_error("TEST", $sformatf("FAIL: addr mismatch - got 0x%08x, expected 0xDEADBEEF", obj2.addr))
            passed = 0;
         end

         if (obj2.data == 8'hAB) begin
            `uvm_info("TEST", "PASS: data matches", UVM_LOW)
         end else begin
            `uvm_error("TEST", $sformatf("FAIL: data mismatch - got 0x%02x, expected 0xAB", obj2.data))
            passed = 0;
         end

         if (obj2.len == 4'd7) begin
            `uvm_info("TEST", "PASS: len matches", UVM_LOW)
         end else begin
            `uvm_error("TEST", $sformatf("FAIL: len mismatch - got %0d, expected 7", obj2.len))
            passed = 0;
         end

         if (obj2.name_str == "test123") begin
            `uvm_info("TEST", "PASS: name_str matches", UVM_LOW)
         end else begin
            `uvm_error("TEST", {"FAIL: name_str mismatch - got '", obj2.name_str, "', expected 'test123'"})
            passed = 0;
         end

         // Test 4: Test big_endian mode
         packer.reset();
         packer.big_endian = 1;
         obj1.pack(packer);
         packer.set_packed_size();
         obj2 = PackableObject::type_id::create("obj2_be");
         obj2.unpack(packer);

         if (obj2.addr == 32'hDEADBEEF && obj2.data == 8'hAB && obj2.len == 4'd7) begin
            `uvm_info("TEST", "PASS: big_endian mode works", UVM_LOW)
         end else begin
            `uvm_error("TEST", "FAIL: big_endian mode mismatch")
            passed = 0;
         end

         if (passed) begin
            `uvm_info("TEST", "All packer tests passed!", UVM_LOW)
         end

         $write("*-* All Finished *-*\n");
         $finish;
      endtask
   endclass

   initial begin
      run_test("test");
   end
endmodule
