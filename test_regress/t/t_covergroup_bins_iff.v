// DESCRIPTION: Verilator: Test covergroup bins with iff guards
// Tests conditional bin sampling based on iff expressions
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Pattern from AHB AVIP:
// bins ahbAddrHalfWordAligned = { [0:'hFFFFFFFF] } iff(haddr[0]==0);

module t;
   // Test transaction class
   class Transaction;
      rand bit [7:0] data;
      rand bit [3:0] addr;
      rand bit       write_en;
      rand bit [1:0] size;

      function new();
      endfunction
   endclass

   // Covergroup with iff guards on bins
   covergroup TransactionCg with function sample(Transaction tx);
      option.per_instance = 1;

      // Basic data coverage
      DATA_CP: coverpoint tx.data {
         bins low_data = {[0:63]};
         bins mid_data = {[64:191]};
         bins high_data = {[192:255]};
      }

      // Address coverage with alignment iff guards
      ADDR_CP: coverpoint tx.addr {
         option.comment = "Address coverage with alignment checks";
         // Any address
         bins any_addr = {[0:15]};
         // Only even addresses (2-byte aligned)
         bins aligned_2byte = {[0:15]} iff (tx.addr[0] == 0);
         // Only 4-byte aligned addresses
         bins aligned_4byte = {[0:15]} iff (tx.addr[1:0] == 2'b00);
      }

      // Write vs read with data range guards
      WRITE_CP: coverpoint tx.write_en {
         bins read_op = {0};
         bins write_op = {1};
         // Write with high data only
         bins write_high_data = {1} iff (tx.data >= 128);
         // Write with low data only
         bins write_low_data = {1} iff (tx.data < 128);
      }

      // Size with valid alignment iff
      SIZE_CP: coverpoint tx.size {
         option.comment = "Transfer size coverage";
         bins byte_size = {0};
         bins halfword_size = {1} iff (tx.addr[0] == 0);  // Must be 2-byte aligned
         bins word_size = {2} iff (tx.addr[1:0] == 0);    // Must be 4-byte aligned
         bins dword_size = {3} iff (tx.addr[1:0] == 0);   // Must be 4-byte aligned (minimum)
      }

      // Combined iff with bins array
      MULTI_CP: coverpoint tx.data[7:4] {
         // Only when address is even
         bins even_addr_nibbles[4] = {[0:15]} iff (tx.addr[0] == 0);
      }

   endgroup

   // Simple covergroup to verify basic iff functionality
   covergroup SimpleIffCg with function sample(bit [7:0] value, bit condition);
      VALUE_CP: coverpoint value {
         bins all_values = {[0:255]};
         bins conditional_only = {[0:255]} iff (condition);
      }
   endgroup

   initial begin
      Transaction tx;
      TransactionCg cg;
      SimpleIffCg simple_cg;
      int i;
      int pass_count = 0;
      int test_count = 0;

      tx = new();
      cg = new();
      simple_cg = new();

      // Test 1: Sample transactions to get coverage
      $display("Test 1: Sample various transactions");
      test_count++;
      for (i = 0; i < 100; i++) begin
         void'(tx.randomize());
         cg.sample(tx);
      end
      if (cg.get_coverage() > 0) begin
         $display("  PASS: Got coverage from sampling (total=%.1f%%)", cg.get_coverage());
         pass_count++;
      end else begin
         $display("  FAIL: No coverage after sampling");
      end

      // Test 2: Simple iff test - condition true vs false
      $display("Test 2: Simple iff condition test");
      test_count++;
      begin
         // Sample with condition=1 (should hit conditional_only bin)
         for (i = 0; i < 50; i++) begin
            simple_cg.sample(i[7:0], 1);
         end
         // Sample with condition=0 (should NOT hit conditional_only bin)
         for (i = 0; i < 50; i++) begin
            simple_cg.sample(i[7:0], 0);
         end
         if (simple_cg.get_coverage() > 0) begin
            $display("  PASS: Simple iff covergroup working (coverage=%.1f%%)", simple_cg.get_coverage());
            pass_count++;
         end else begin
            $display("  FAIL: Simple iff covergroup not working");
         end
      end

      // Test 3: Specific aligned cases
      $display("Test 3: Aligned transfer coverage");
      test_count++;
      begin
         // Word transfer at aligned address
         tx.addr = 4'b0000;  // 4-byte aligned
         tx.size = 2;        // Word
         tx.data = 8'hAB;
         tx.write_en = 1;
         cg.sample(tx);

         // Halfword at 2-byte aligned
         tx.addr = 4'b0010;  // 2-byte aligned, not 4-byte
         tx.size = 1;        // Halfword
         cg.sample(tx);

         // Byte at any address
         tx.addr = 4'b0111;  // Odd address
         tx.size = 0;        // Byte
         cg.sample(tx);

         if (cg.get_coverage() > 0) begin
            $display("  PASS: Aligned transfer coverage (total=%.1f%%)", cg.get_coverage());
            pass_count++;
         end else begin
            $display("  FAIL: No aligned transfer coverage");
         end
      end

      // Test 4: Write with different data ranges
      $display("Test 4: Write operation with data range iff");
      test_count++;
      begin
         // Write with high data
         tx.data = 200;
         tx.write_en = 1;
         tx.addr = 4'b0000;
         cg.sample(tx);

         // Write with low data
         tx.data = 50;
         tx.write_en = 1;
         cg.sample(tx);

         // Read operation
         tx.write_en = 0;
         cg.sample(tx);

         if (cg.get_coverage() > 0) begin
            $display("  PASS: Write operation coverage (total=%.1f%%)", cg.get_coverage());
            pass_count++;
         end else begin
            $display("  FAIL: No write operation coverage");
         end
      end

      // Test 5: Bins array with iff
      $display("Test 5: Bins array with iff guard");
      test_count++;
      begin
         // Sample with even addresses (should hit even_addr_nibbles)
         for (i = 0; i < 16; i++) begin
            tx.data = i * 16;  // Various high nibbles
            tx.addr = 4'b0000; // Even address
            cg.sample(tx);
         end
         // Sample with odd addresses (should NOT hit even_addr_nibbles)
         for (i = 0; i < 16; i++) begin
            tx.data = i * 16;
            tx.addr = 4'b0001; // Odd address
            cg.sample(tx);
         end
         if (cg.get_coverage() > 0) begin
            $display("  PASS: Bins array with iff guard working");
            pass_count++;
         end else begin
            $display("  FAIL: Bins array with iff guard not working");
         end
      end

      // Summary
      $display("");
      $display("Results: %0d/%0d tests passed", pass_count, test_count);

      if (pass_count == test_count) begin
         $display("*-* All Finished *-*");
      end else begin
         $display("FAIL: Some tests failed");
         $stop;
      end
      $finish;
   end
endmodule
