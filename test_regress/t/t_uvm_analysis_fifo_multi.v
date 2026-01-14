// DESCRIPTION: Verilator: Test UVM analysis FIFO with multiple writers
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test uvm_tlm_analysis_fifo with multiple analysis ports writing to it
// This pattern is commonly used in UVM scoreboards

module t;
    import uvm_pkg::*;
    `include "uvm_macros.svh"

    // Simple transaction class
    class my_transaction extends uvm_sequence_item;
        int data;
        string source;

        `uvm_object_utils_begin(my_transaction)
            `uvm_field_int(data, UVM_ALL_ON)
            `uvm_field_string(source, UVM_ALL_ON)
        `uvm_object_utils_end

        function new(string name = "my_transaction");
            super.new(name);
        endfunction
    endclass

    // Monitor that broadcasts transactions
    class my_monitor extends uvm_component;
        uvm_analysis_port #(my_transaction) ap;
        string monitor_name;

        `uvm_component_utils(my_monitor)

        function new(string name, uvm_component parent);
            super.new(name, parent);
            ap = new("ap", this);
            monitor_name = name;
        endfunction

        task send_transaction(int data);
            my_transaction tx = new();
            tx.data = data;
            tx.source = monitor_name;
            ap.write(tx);
        endtask
    endclass

    // Scoreboard that receives transactions via analysis port write
    class my_scoreboard extends uvm_component;
        uvm_analysis_imp #(my_transaction, my_scoreboard) analysis_export;
        int received_count;

        `uvm_component_utils(my_scoreboard)

        function new(string name, uvm_component parent);
            super.new(name, parent);
            analysis_export = new("analysis_export", this);
            received_count = 0;
        endfunction

        // Called when transaction is written to analysis port
        function void write(my_transaction tx);
            `uvm_info("SCOREBOARD", $sformatf("Received: data=%0d from %s",
                      tx.data, tx.source), UVM_MEDIUM)
            received_count++;
        endfunction

        function void check_phase(uvm_phase phase);
            if (received_count != 6) begin
                `uvm_error("SCOREBOARD", $sformatf("Expected 6 transactions, got %0d", received_count))
            end else begin
                `uvm_info("SCOREBOARD", "Received all 6 expected transactions", UVM_LOW)
            end
        endfunction
    endclass

    // Environment connecting monitors to scoreboard
    class my_env extends uvm_env;
        my_monitor mon1, mon2;
        my_scoreboard sb;

        `uvm_component_utils(my_env)

        function new(string name, uvm_component parent);
            super.new(name, parent);
        endfunction

        function void build_phase(uvm_phase phase);
            super.build_phase(phase);
            mon1 = my_monitor::type_id::create("mon1", this);
            mon2 = my_monitor::type_id::create("mon2", this);
            sb = my_scoreboard::type_id::create("sb", this);
        endfunction

        function void connect_phase(uvm_phase phase);
            super.connect_phase(phase);
            // Both monitors write to same scoreboard
            mon1.ap.connect(sb.analysis_export);
            mon2.ap.connect(sb.analysis_export);
        endfunction

        task run_phase(uvm_phase phase);
            phase.raise_objection(this);

            // Both monitors send transactions sequentially
            mon1.send_transaction(100);
            mon1.send_transaction(200);
            mon1.send_transaction(300);
            mon2.send_transaction(1000);
            mon2.send_transaction(2000);
            mon2.send_transaction(3000);

            // Check count and finish
            if (sb.received_count != 6) begin
                `uvm_error("ENV", $sformatf("Expected 6 transactions, got %0d", sb.received_count))
            end else begin
                `uvm_info("ENV", "All 6 transactions received successfully", UVM_LOW)
            end

            $write("*-* All Finished *-*\n");
            $finish;
        endtask
    endclass

    // Test
    class my_test extends uvm_test;
        my_env env;

        `uvm_component_utils(my_test)

        function new(string name, uvm_component parent);
            super.new(name, parent);
        endfunction

        function void build_phase(uvm_phase phase);
            super.build_phase(phase);
            env = my_env::type_id::create("env", this);
        endfunction
    endclass

    initial begin
        run_test("my_test");
    end
endmodule
