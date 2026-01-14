// DESCRIPTION: Verilator: Verilog Test module
//
// Test semaphore-based synchronization - pattern from AVIPs
// Tests semaphore get/put/try_get operations
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Anthropic.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t_semaphore_multichannel;
    semaphore sem;
    int producer_count = 0;
    int consumer_count = 0;

    // Test basic operations
    task automatic test_basic();
        semaphore s;
        int result;

        $display("\n=== Test 1: Basic operations ===");
        s = new(2);

        // try_get should succeed twice
        result = s.try_get(1);
        `checkh(result, 1)
        $display("try_get(1): %0d (expected 1)", result);

        result = s.try_get(1);
        `checkh(result, 1)
        $display("try_get(1): %0d (expected 1)", result);

        // try_get should fail now
        result = s.try_get(1);
        `checkh(result, 0)
        $display("try_get(1): %0d (expected 0)", result);

        // put and try_get
        s.put(3);
        result = s.try_get(2);
        `checkh(result, 1)
        $display("try_get(2) after put(3): %0d (expected 1)", result);

        result = s.try_get(2);
        `checkh(result, 0)
        $display("try_get(2): %0d (expected 0, only 1 left)", result);

        result = s.try_get(1);
        `checkh(result, 1)
        $display("try_get(1): %0d (expected 1)", result);
    endtask

    // Test producer-consumer with fork/join
    task automatic test_producer_consumer();
        int produced = 0;
        int consumed = 0;

        $display("\n=== Test 2: Producer-consumer ===");
        sem = new(0);

        fork
            // Producer
            begin
                repeat(3) begin
                    #2;
                    produced++;
                    sem.put(1);
                    $display("[%0t] Produced item %0d", $time, produced);
                end
            end
            // Consumer
            begin
                repeat(3) begin
                    sem.get(1);
                    consumed++;
                    $display("[%0t] Consumed item %0d", $time, consumed);
                    #1;
                end
            end
        join

        `checkh(produced, 3)
        `checkh(consumed, 3)
        $display("Producer-consumer completed: %0d produced, %0d consumed", produced, consumed);
    endtask

    // Test mutual exclusion
    task automatic test_mutual_exclusion();
        semaphore mutex;
        int shared_var = 0;
        int task1_count = 0;
        int task2_count = 0;

        $display("\n=== Test 3: Mutual exclusion ===");
        mutex = new(1);  // Binary semaphore

        fork
            // Task 1
            begin
                repeat(3) begin
                    mutex.get(1);
                    task1_count++;
                    shared_var = 100 + task1_count;
                    $display("[%0t] Task1 has mutex, shared=%0d", $time, shared_var);
                    #2;
                    mutex.put(1);
                    #1;
                end
            end
            // Task 2
            begin
                repeat(3) begin
                    mutex.get(1);
                    task2_count++;
                    shared_var = 200 + task2_count;
                    $display("[%0t] Task2 has mutex, shared=%0d", $time, shared_var);
                    #2;
                    mutex.put(1);
                    #1;
                end
            end
        join

        `checkh(task1_count, 3)
        `checkh(task2_count, 3)
        $display("Mutual exclusion completed: task1=%0d, task2=%0d", task1_count, task2_count);
    endtask

    // Test multiple keys
    task automatic test_multiple_keys();
        semaphore pool;
        int results[4];

        $display("\n=== Test 4: Multiple keys (resource pool) ===");
        pool = new(2);  // 2 resources available

        fork
            begin
                pool.get(1);
                $display("[%0t] Worker 0 acquired resource", $time);
                #3;
                results[0] = 1;
                pool.put(1);
                $display("[%0t] Worker 0 released resource", $time);
            end
            begin
                pool.get(1);
                $display("[%0t] Worker 1 acquired resource", $time);
                #2;
                results[1] = 1;
                pool.put(1);
                $display("[%0t] Worker 1 released resource", $time);
            end
            begin
                pool.get(1);
                $display("[%0t] Worker 2 acquired resource", $time);
                #4;
                results[2] = 1;
                pool.put(1);
                $display("[%0t] Worker 2 released resource", $time);
            end
            begin
                pool.get(1);
                $display("[%0t] Worker 3 acquired resource", $time);
                #1;
                results[3] = 1;
                pool.put(1);
                $display("[%0t] Worker 3 released resource", $time);
            end
        join

        `checkh(results[0], 1)
        `checkh(results[1], 1)
        `checkh(results[2], 1)
        `checkh(results[3], 1)
        $display("Resource pool test completed");
    endtask

    initial begin
        $display("Test: Semaphore synchronization (AVIP pattern)");

        test_basic();
        test_producer_consumer();
        test_mutual_exclusion();
        test_multiple_keys();

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
