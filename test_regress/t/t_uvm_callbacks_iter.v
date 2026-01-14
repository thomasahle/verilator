// DESCRIPTION: Verilator: Verilog Test module
//
// Test uvm_callbacks iteration and invocation
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`include "uvm_macros.svh"

module t;
   import uvm_pkg::*;

   // Custom callback class
   class my_callback extends uvm_callback;
      string cb_name;
      static int invoke_count;

      function new(string name = "my_callback");
         super.new(name);
         cb_name = name;
      endfunction

      virtual function void pre_action(string msg);
         invoke_count++;
         $display("[CB:%s] pre_action called with msg='%s', invoke_count=%0d", cb_name, msg, invoke_count);
      endfunction

      virtual function void post_action(int result);
         invoke_count++;
         $display("[CB:%s] post_action called with result=%0d, invoke_count=%0d", cb_name, result, invoke_count);
      endfunction
   endclass

   // Component that uses callbacks
   class my_component extends uvm_component;
      `uvm_component_utils(my_component)

      function new(string name, uvm_component parent);
         super.new(name, parent);
      endfunction

      function void do_action(string msg);
         my_callback cb;
         my_callback cbs[$];
         int iter;

         // Invoke pre_action on all callbacks
         uvm_callbacks#(my_component, my_callback)::get(this, cbs);
         foreach (cbs[i]) begin
            cbs[i].pre_action(msg);
         end

         // Do the actual action
         $display("[COMP] Doing action: %s", msg);

         // Invoke post_action on all callbacks
         foreach (cbs[i]) begin
            cbs[i].post_action(42);
         end
      endfunction

      // Alternative iteration using has_callbacks check
      function void do_action_iter(string msg);
         my_callback cbs[$];

         // Check if has callbacks before getting
         if (uvm_callbacks#(my_component, my_callback)::has_callbacks(this)) begin
            uvm_callbacks#(my_component, my_callback)::get(this, cbs);
            foreach (cbs[i]) begin
               cbs[i].pre_action(msg);
            end
         end

         $display("[COMP] Doing action (iter): %s", msg);
      endfunction
   endclass

   // Test component
   class test extends uvm_test;
      `uvm_component_utils(test)

      my_component comp;

      function new(string name, uvm_component parent);
         super.new(name, parent);
      endfunction

      function void build_phase(uvm_phase phase);
         super.build_phase(phase);
         comp = my_component::type_id::create("comp", this);
      endfunction

      task run_phase(uvm_phase phase);
         my_callback cb1, cb2, cb3;
         bit passed = 1;

         phase.raise_objection(this);

         // Reset invoke count
         my_callback::invoke_count = 0;

         // Test 1: Check initially no callbacks
         if (!uvm_callbacks#(my_component, my_callback)::has_callbacks(comp)) begin
            `uvm_info("TEST", "PASS: initially no callbacks", UVM_LOW)
         end else begin
            `uvm_error("TEST", "FAIL: should have no callbacks initially")
            passed = 0;
         end

         // Test 2: Add callbacks
         cb1 = new("callback_1");
         cb2 = new("callback_2");
         cb3 = new("callback_3");

         uvm_callbacks#(my_component, my_callback)::add(comp, cb1);
         uvm_callbacks#(my_component, my_callback)::add(comp, cb2);
         uvm_callbacks#(my_component, my_callback)::add(comp, cb3);

         if (uvm_callbacks#(my_component, my_callback)::get_count(comp) == 3) begin
            `uvm_info("TEST", "PASS: 3 callbacks registered", UVM_LOW)
         end else begin
            `uvm_error("TEST", "FAIL: callback count mismatch")
            passed = 0;
         end

         // Test 3: Invoke callbacks via get() pattern
         `uvm_info("TEST", "Testing get() pattern:", UVM_LOW)
         comp.do_action("test_message");

         // Each callback should have been invoked twice (pre + post)
         // 3 callbacks * 2 invocations = 6
         if (my_callback::invoke_count == 6) begin
            `uvm_info("TEST", "PASS: all callbacks invoked correctly", UVM_LOW)
         end else begin
            `uvm_error("TEST", $sformatf("FAIL: invoke_count=%0d, expected 6", my_callback::invoke_count))
            passed = 0;
         end

         // Test 4: Invoke callbacks via has_callbacks check pattern
         `uvm_info("TEST", "Testing has_callbacks pattern:", UVM_LOW)
         my_callback::invoke_count = 0;
         comp.do_action_iter("iter_message");

         // 3 callbacks * 1 invocation = 3
         if (my_callback::invoke_count == 3) begin
            `uvm_info("TEST", "PASS: has_callbacks pattern works", UVM_LOW)
         end else begin
            `uvm_error("TEST", $sformatf("FAIL: invoke_count=%0d, expected 3", my_callback::invoke_count))
            passed = 0;
         end

         // Test 5: Disable a callback
         cb2.set_enabled(0);
         my_callback::invoke_count = 0;
         comp.do_action_iter("disabled_test");

         // 2 enabled callbacks * 1 invocation = 2
         if (my_callback::invoke_count == 2) begin
            `uvm_info("TEST", "PASS: disabled callback skipped", UVM_LOW)
         end else begin
            `uvm_error("TEST", $sformatf("FAIL: invoke_count=%0d, expected 2", my_callback::invoke_count))
            passed = 0;
         end

         // Test 6: Delete a callback
         uvm_callbacks#(my_component, my_callback)::delete(comp, cb1);
         if (uvm_callbacks#(my_component, my_callback)::get_count(comp) == 1) begin
            `uvm_info("TEST", "PASS: callback deleted (1 remaining enabled)", UVM_LOW)
         end else begin
            `uvm_error("TEST", "FAIL: delete didn't work")
            passed = 0;
         end

         // Test 7: Display callbacks
         `uvm_info("TEST", "Displaying callbacks:", UVM_LOW)
         uvm_callbacks#(my_component, my_callback)::display(comp);

         if (passed) begin
            `uvm_info("TEST", "All callback tests passed!", UVM_LOW)
         end

         $write("*-* All Finished *-*\n");
         $finish;
      endtask
   endclass

   initial begin
      run_test("test");
   end
endmodule
