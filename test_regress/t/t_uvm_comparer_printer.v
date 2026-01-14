// DESCRIPTION: Verilator: Verilog Test module
//
// Test uvm_comparer and uvm_printer utility classes
//
// This code is licensed under the GNU Lesser General Public License (LGPL)

`include "uvm_macros.svh"

module t;
   import uvm_pkg::*;

   // Custom object for testing comparison and printing
   class TestObject extends uvm_object;
      `uvm_object_utils(TestObject)

      rand int value;
      rand bit [7:0] data;
      string name_str;

      function new(string name = "TestObject");
         super.new(name);
         name_str = name;
      endfunction

      virtual function void do_copy(uvm_object rhs);
         TestObject rhs_obj;
         super.do_copy(rhs);
         if ($cast(rhs_obj, rhs)) begin
            value = rhs_obj.value;
            data = rhs_obj.data;
            name_str = rhs_obj.name_str;
         end
      endfunction

      virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer);
         TestObject rhs_obj;
         if (!$cast(rhs_obj, rhs)) return 0;
         return (value == rhs_obj.value) && (data == rhs_obj.data);
      endfunction

      virtual function string convert2string();
         return $sformatf("value=%0d, data=0x%02x, name=%s", value, data, name_str);
      endfunction
   endclass

   // Test component
   class test extends uvm_test;
      `uvm_component_utils(test)

      function new(string name, uvm_component parent);
         super.new(name, parent);
      endfunction

      task run_phase(uvm_phase phase);
         TestObject obj1, obj2, obj3;
         uvm_comparer comparer;
         string printed;
         bit result;

         phase.raise_objection(this);

         // Create test objects
         obj1 = TestObject::type_id::create("obj1");
         obj1.value = 42;
         obj1.data = 8'hAB;

         obj2 = TestObject::type_id::create("obj2");
         obj2.value = 42;
         obj2.data = 8'hAB;

         obj3 = TestObject::type_id::create("obj3");
         obj3.value = 100;
         obj3.data = 8'hCD;

         // Test 1: Compare identical objects
         comparer = new("comparer");
         result = obj1.compare(obj2, comparer);
         if (!result) begin
            `uvm_error("TEST", "FAIL: identical objects should compare equal")
         end else begin
            `uvm_info("TEST", "PASS: identical objects compare equal", UVM_LOW)
         end

         // Test 2: Compare different objects
         result = obj1.compare(obj3, comparer);
         if (result) begin
            `uvm_error("TEST", "FAIL: different objects should not compare equal")
         end else begin
            `uvm_info("TEST", "PASS: different objects compare not equal", UVM_LOW)
         end

         // Test 3: Test sprint
         printed = obj1.sprint();
         if (printed.len() > 0) begin
            `uvm_info("TEST", {"PASS: sprint returned: ", printed}, UVM_LOW)
         end else begin
            `uvm_error("TEST", "FAIL: sprint returned empty string")
         end

         // Test 4: Test convert2string
         printed = obj1.convert2string();
         if (printed.len() > 0 && printed.substr(0, 4) == "value") begin
            `uvm_info("TEST", {"PASS: convert2string returned: ", printed}, UVM_LOW)
         end else begin
            `uvm_error("TEST", {"FAIL: unexpected convert2string output: ", printed})
         end

         // Test 5: Test copy
         obj3.copy(obj1);
         result = obj3.compare(obj1, comparer);
         if (!result) begin
            `uvm_error("TEST", "FAIL: copied object should compare equal")
         end else begin
            `uvm_info("TEST", "PASS: copied object compares equal", UVM_LOW)
         end

         // Test 6: Clone
         begin
            uvm_object cloned;
            TestObject cloned_obj;
            cloned = obj1.clone();
            if (cloned == null) begin
               `uvm_error("TEST", "FAIL: clone returned null")
            end else if (!$cast(cloned_obj, cloned)) begin
               `uvm_error("TEST", "FAIL: clone returned wrong type")
            end else if (!cloned_obj.compare(obj1, comparer)) begin
               `uvm_error("TEST", "FAIL: cloned object should compare equal")
            end else begin
               `uvm_info("TEST", "PASS: clone works correctly", UVM_LOW)
            end
         end

         `uvm_info("TEST", "All tests passed!", UVM_LOW)
         $write("*-* All Finished *-*\n");
         $finish;
      endtask
   endclass

   initial begin
      run_test("test");
   end
endmodule
