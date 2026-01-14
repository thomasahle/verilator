// DESCRIPTION: Verilator: Test UVM barrier synchronization
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test uvm_barrier for process synchronization

module t;
    import uvm_pkg::*;
    `include "uvm_macros.svh"

    // Test component that uses barriers
    class barrier_test extends uvm_test;
        uvm_barrier bar;

        `uvm_component_utils(barrier_test)

        function new(string name, uvm_component parent);
            super.new(name, parent);
            bar = new("test_barrier", 3);  // Threshold of 3
        endfunction

        task run_phase(uvm_phase phase);
            phase.raise_objection(this);

            // Test 1: Basic threshold and auto-reset
            `uvm_info("TEST", $sformatf("Barrier threshold: %0d", bar.get_threshold()), UVM_LOW)
            if (bar.get_threshold() != 3) begin
                `uvm_error("TEST", "Threshold should be 3")
            end

            // Test auto-reset default
            if (!bar.get_auto_reset()) begin
                `uvm_error("TEST", "Auto-reset should be enabled by default")
            end else begin
                `uvm_info("TEST", "Auto-reset is enabled by default - PASS", UVM_LOW)
            end

            // Test 2: Reset and change threshold
            bar.reset();
            bar.set_threshold(2);
            if (bar.get_threshold() != 2) begin
                `uvm_error("TEST", "Threshold should be 2 after set")
            end else begin
                `uvm_info("TEST", "set_threshold() works - PASS", UVM_LOW)
            end

            // Test 3: Set auto-reset to false
            bar.set_auto_reset(0);
            if (bar.get_auto_reset()) begin
                `uvm_error("TEST", "Auto-reset should be disabled")
            end else begin
                `uvm_info("TEST", "set_auto_reset() works - PASS", UVM_LOW)
            end

            // Test 4: Get number of waiters (should be 0 initially)
            if (bar.get_num_waiters() != 0) begin
                `uvm_error("TEST", "Initial num_waiters should be 0")
            end else begin
                `uvm_info("TEST", "get_num_waiters() returns 0 initially - PASS", UVM_LOW)
            end

            `uvm_info("TEST", "All barrier API tests passed!", UVM_LOW)

            $write("*-* All Finished *-*\n");
            $finish;
        endtask
    endclass

    initial begin
        run_test("barrier_test");
    end
endmodule
