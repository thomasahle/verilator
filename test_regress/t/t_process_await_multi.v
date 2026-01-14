// DESCRIPTION: Verilator: Verilog Test module
//
// Test process::await() with multiple processes - pattern from AVIPs
// Tests process synchronization patterns
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Anthropic.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t_process_await_multi;
    import std::*;

    int results[4];
    int completion_count = 0;

    // Simple task that completes after a delay
    task automatic do_work(input int id, input int delay_cycles, output int result);
        $display("[%0t] Task %0d started", $time, id);
        repeat(delay_cycles) #1;
        result = id * 10 + delay_cycles;
        $display("[%0t] Task %0d completed with result %0d", $time, id, result);
    endtask

    // Test basic fork/join synchronization
    task automatic test_fork_join();
        $display("\n=== Test 1: Basic fork/join ===");

        fork
            do_work(0, 3, results[0]);
            do_work(1, 1, results[1]);
            do_work(2, 5, results[2]);
            do_work(3, 2, results[3]);
        join

        $display("[%0t] All tasks joined", $time);
        `checkh(results[0], 3)   // 0*10 + 3
        `checkh(results[1], 11)  // 1*10 + 1
        `checkh(results[2], 25)  // 2*10 + 5
        `checkh(results[3], 32)  // 3*10 + 2
    endtask

    // Test wait fork
    task automatic test_wait_fork();
        $display("\n=== Test 2: Wait fork ===");

        // Reset results
        results[0] = 0;
        results[1] = 0;

        fork
            do_work(0, 4, results[0]);
            do_work(1, 2, results[1]);
        join_none

        $display("[%0t] fork/join_none done, waiting for fork", $time);
        wait fork;
        $display("[%0t] wait fork completed", $time);

        `checkh(results[0], 4)
        `checkh(results[1], 12)
    endtask

    // Test process status
    task automatic test_process_status();
        process p;

        $display("\n=== Test 3: Process status ===");

        fork
            begin
                p = process::self();
                $display("[%0t] Process captured, status=%0d", $time, p.status());
                #5;
                $display("[%0t] Process finishing", $time);
            end
        join_none

        #1;
        if (p != null) begin
            $display("[%0t] Process status during run: %0d", $time, p.status());
        end

        wait fork;

        if (p != null) begin
            $display("[%0t] Process status after completion: %0d", $time, p.status());
            `checkh(p.status(), process::FINISHED)
        end
    endtask

    // Test process await
    task automatic test_process_await();
        process p;
        int value = 0;

        $display("\n=== Test 4: Process await ===");

        fork
            begin
                p = process::self();
                repeat(3) begin
                    #1;
                    value++;
                end
            end
        join_none

        #1;  // Let process start
        if (p != null) begin
            $display("[%0t] Awaiting process, value=%0d", $time, value);
            p.await();
            $display("[%0t] Process awaited, value=%0d", $time, value);
            `checkh(value, 3)
        end else begin
            wait fork;  // Fallback
            `checkh(value, 3)
        end
    endtask

    initial begin
        $display("Test: Process await with multiple processes (AVIP pattern)");

        test_fork_join();
        test_wait_fork();
        test_process_status();
        test_process_await();

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
