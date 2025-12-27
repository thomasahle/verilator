// DESCRIPTION: Verilator: Test UVM pool and queue utilities
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test uvm_pool and uvm_queue container classes

`include "uvm_macros.svh"

module t;
  import uvm_pkg::*;

  // Test item class
  class test_item extends uvm_object;
    `uvm_object_utils(test_item)
    int value;

    function new(string name = "test_item");
      super.new(name);
    endfunction
  endclass

  // Test uvm_pool with string keys
  task automatic test_pool_string();
    uvm_pool #(string, test_item) pool;
    test_item item1, item2, item3, retrieved;
    string key;

    $display("[%0t] test_pool_string: Starting", $time);

    pool = new("string_pool");

    // Create items
    item1 = new("item1");
    item1.value = 100;
    item2 = new("item2");
    item2.value = 200;
    item3 = new("item3");
    item3.value = 300;

    // Add items
    pool.add("key1", item1);
    pool.add("key2", item2);
    pool.add("key3", item3);

    if (pool.num() != 3) begin
      $display("ERROR: Expected 3 items, got %0d", pool.num());
      $stop;
    end
    $display("[%0t] Pool has %0d items", $time, pool.num());

    // Check exists
    if (!pool.exists("key1")) begin
      $display("ERROR: key1 should exist");
      $stop;
    end
    if (pool.exists("nonexistent")) begin
      $display("ERROR: nonexistent should not exist");
      $stop;
    end

    // Get items
    retrieved = pool.get("key2");
    if (retrieved == null || retrieved.value != 200) begin
      $display("ERROR: Failed to get key2 with value 200");
      $stop;
    end
    $display("[%0t] Retrieved key2 with value=%0d", $time, retrieved.value);

    // Delete
    pool.delete("key2");
    if (pool.exists("key2")) begin
      $display("ERROR: key2 should be deleted");
      $stop;
    end
    if (pool.num() != 2) begin
      $display("ERROR: Expected 2 items after delete");
      $stop;
    end
    $display("[%0t] After delete: %0d items", $time, pool.num());

    // Iterate with first/next
    if (pool.first(key)) begin
      $display("[%0t] First key: %s", $time, key);
      while (pool.next(key)) begin
        $display("[%0t] Next key: %s", $time, key);
      end
    end

    $display("[%0t] test_pool_string: PASSED", $time);
  endtask

  // Test uvm_pool with int keys
  task automatic test_pool_int();
    uvm_pool #(int, test_item) pool;
    test_item item;
    int key;

    $display("[%0t] test_pool_int: Starting", $time);

    pool = new("int_pool");

    // Add items with int keys
    for (int i = 0; i < 5; i++) begin
      item = new($sformatf("item%0d", i));
      item.value = i * 10;
      pool.add(i, item);
    end

    if (pool.num() != 5) begin
      $display("ERROR: Expected 5 items");
      $stop;
    end

    // Get item
    item = pool.get(3);
    if (item.value != 30) begin
      $display("ERROR: Expected value 30, got %0d", item.value);
      $stop;
    end
    $display("[%0t] Item 3 has value=%0d", $time, item.value);

    $display("[%0t] test_pool_int: PASSED", $time);
  endtask

  // Test uvm_queue
  task automatic test_queue();
    uvm_queue #(test_item) queue;
    test_item item, popped;

    $display("[%0t] test_queue: Starting", $time);

    queue = new("test_queue");

    // Push items
    for (int i = 0; i < 5; i++) begin
      item = new($sformatf("q_item%0d", i));
      item.value = i;
      queue.push_back(item);
    end

    if (queue.size() != 5) begin
      $display("ERROR: Expected size 5, got %0d", queue.size());
      $stop;
    end
    $display("[%0t] Queue size: %0d", $time, queue.size());

    // Get by index
    item = queue.get(2);
    if (item.value != 2) begin
      $display("ERROR: Expected value 2 at index 2");
      $stop;
    end
    $display("[%0t] Item at index 2: value=%0d", $time, item.value);

    // Pop front (should be 0)
    popped = queue.pop_front();
    if (popped.value != 0) begin
      $display("ERROR: Expected pop_front to return value 0");
      $stop;
    end
    $display("[%0t] Popped front: value=%0d, remaining=%0d", $time, popped.value, queue.size());

    // Pop back (should be 4)
    popped = queue.pop_back();
    if (popped.value != 4) begin
      $display("ERROR: Expected pop_back to return value 4");
      $stop;
    end
    $display("[%0t] Popped back: value=%0d, remaining=%0d", $time, popped.value, queue.size());

    // Push front
    item = new("front_item");
    item.value = 99;
    queue.push_front(item);

    popped = queue.get(0);
    if (popped.value != 99) begin
      $display("ERROR: Expected front item value 99");
      $stop;
    end
    $display("[%0t] Front item after push_front: value=%0d", $time, popped.value);

    // Insert at index
    item = new("inserted");
    item.value = 50;
    queue.insert(2, item);

    popped = queue.get(2);
    if (popped.value != 50) begin
      $display("ERROR: Expected inserted item value 50 at index 2");
      $stop;
    end
    $display("[%0t] Item at index 2 after insert: value=%0d, size=%0d", $time, popped.value, queue.size());

    // Delete specific index
    queue.delete(2);
    if (queue.size() != 4) begin
      $display("ERROR: Expected size 4 after delete");
      $stop;
    end
    $display("[%0t] Size after delete(2): %0d", $time, queue.size());

    // Delete all
    queue.delete(-1);
    if (queue.size() != 0) begin
      $display("ERROR: Expected empty queue after delete(-1)");
      $stop;
    end
    $display("[%0t] Size after delete all: %0d", $time, queue.size());

    $display("[%0t] test_queue: PASSED", $time);
  endtask

  initial begin
    $display("=== UVM Pool and Queue Tests ===");

    test_pool_string();
    #10;

    test_pool_int();
    #10;

    test_queue();

    $display("\n=== All Tests PASSED ===");
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
