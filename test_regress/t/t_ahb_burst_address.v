// DESCRIPTION: Verilator: Test AHB-style burst address calculation
// Tests WRAP/INCR burst address generation patterns used in bus protocols
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
   // AHB Burst types
   typedef enum bit [2:0] {
      SINGLE = 3'b000,
      INCR   = 3'b001,
      WRAP4  = 3'b010,
      INCR4  = 3'b011,
      WRAP8  = 3'b100,
      INCR8  = 3'b101,
      WRAP16 = 3'b110,
      INCR16 = 3'b111
   } burst_type_e;

   // AHB Size (transfer width)
   typedef enum bit [2:0] {
      BYTE     = 3'b000,  // 1 byte
      HALFWORD = 3'b001,  // 2 bytes
      WORD     = 3'b010,  // 4 bytes
      DWORD    = 3'b011   // 8 bytes
   } transfer_size_e;

   // Address calculator class
   class BurstAddressCalc;
      bit [31:0] start_address;
      burst_type_e burst_type;
      transfer_size_e transfer_size;
      int beat_count;

      // Current state
      bit [31:0] current_address;
      int current_beat;

      function new();
         start_address = 0;
         burst_type = SINGLE;
         transfer_size = WORD;
         beat_count = 1;
         current_address = 0;
         current_beat = 0;
      endfunction

      // Initialize burst
      function void init(bit [31:0] addr, burst_type_e btype, transfer_size_e tsize);
         start_address = addr;
         burst_type = btype;
         transfer_size = tsize;
         current_address = addr;
         current_beat = 0;

         // Calculate beat count based on burst type
         case (btype)
            SINGLE: beat_count = 1;
            INCR:   beat_count = 1;  // Undefined length, use 1
            WRAP4, INCR4:  beat_count = 4;
            WRAP8, INCR8:  beat_count = 8;
            WRAP16, INCR16: beat_count = 16;
         endcase
      endfunction

      // Get transfer size in bytes
      function int get_size_bytes();
         return (1 << transfer_size);
      endfunction

      // Get wrap boundary mask
      function bit [31:0] get_wrap_mask();
         int burst_bytes = beat_count * get_size_bytes();
         return burst_bytes - 1;
      endfunction

      // Calculate next address - THE CORE ALGORITHM FROM AHB SPEC
      function bit [31:0] next_address();
         bit [31:0] next_addr;
         int size_bytes = get_size_bytes();

         current_beat++;

         if (current_beat >= beat_count) begin
            // Burst complete
            return current_address;
         end

         // Check if WRAP burst
         if (burst_type == WRAP4 || burst_type == WRAP8 || burst_type == WRAP16) begin
            // WRAP burst: address wraps at boundary
            bit [31:0] wrap_mask = get_wrap_mask();
            bit [31:0] aligned_base = current_address & ~wrap_mask;
            bit [31:0] offset = (current_address + size_bytes) & wrap_mask;
            next_addr = aligned_base | offset;
         end else begin
            // INCR burst: simple increment
            next_addr = current_address + size_bytes;
         end

         current_address = next_addr;
         return next_addr;
      endfunction

      // Reset to start
      function void reset();
         current_address = start_address;
         current_beat = 0;
      endfunction
   endclass

   // Test helper: generate expected WRAP addresses
   function automatic void get_wrap_sequence(
      input bit [31:0] start_addr,
      input int burst_len,
      input int size_bytes,
      output bit [31:0] addrs[]
   );
      bit [31:0] wrap_mask = (burst_len * size_bytes) - 1;
      bit [31:0] aligned_base = start_addr & ~wrap_mask;
      bit [31:0] offset = start_addr & wrap_mask;

      addrs = new[burst_len];
      for (int i = 0; i < burst_len; i++) begin
         addrs[i] = aligned_base | offset;
         offset = (offset + size_bytes) & wrap_mask;
      end
   endfunction

   // Test helper: generate expected INCR addresses
   function automatic void get_incr_sequence(
      input bit [31:0] start_addr,
      input int burst_len,
      input int size_bytes,
      output bit [31:0] addrs[]
   );
      addrs = new[burst_len];
      for (int i = 0; i < burst_len; i++) begin
         addrs[i] = start_addr + (i * size_bytes);
      end
   endfunction

   initial begin
      BurstAddressCalc calc;
      bit [31:0] expected_addrs[];
      bit [31:0] actual_addrs[];
      int pass_count = 0;
      int test_count = 0;

      calc = new();

      // Test 1: Simple INCR4 burst from aligned address
      $display("Test 1: INCR4 burst (word size) from aligned address");
      calc.init(32'h1000, INCR4, WORD);
      get_incr_sequence(32'h1000, 4, 4, expected_addrs);

      actual_addrs = new[4];
      actual_addrs[0] = calc.current_address;
      for (int i = 1; i < 4; i++) begin
         actual_addrs[i] = calc.next_address();
      end

      test_count++;
      if (actual_addrs == expected_addrs) begin
         $display("  PASS: %h %h %h %h", actual_addrs[0], actual_addrs[1],
                  actual_addrs[2], actual_addrs[3]);
         pass_count++;
      end else begin
         $display("  FAIL: Expected %h %h %h %h",
                  expected_addrs[0], expected_addrs[1], expected_addrs[2], expected_addrs[3]);
         $display("        Got      %h %h %h %h",
                  actual_addrs[0], actual_addrs[1], actual_addrs[2], actual_addrs[3]);
      end

      // Test 2: WRAP4 burst with wrap-around
      $display("Test 2: WRAP4 burst (word size) starting near boundary");
      // Start at 0x100C, should wrap at 0x1010 back to 0x1000
      calc.init(32'h100C, WRAP4, WORD);
      get_wrap_sequence(32'h100C, 4, 4, expected_addrs);

      actual_addrs[0] = calc.current_address;
      for (int i = 1; i < 4; i++) begin
         actual_addrs[i] = calc.next_address();
      end

      test_count++;
      // Expected: 0x100C, 0x1000, 0x1004, 0x1008 (wraps at 16-byte boundary)
      if (actual_addrs[0] == 32'h100C && actual_addrs[1] == 32'h1000 &&
          actual_addrs[2] == 32'h1004 && actual_addrs[3] == 32'h1008) begin
         $display("  PASS: %h %h %h %h (wraps correctly)", actual_addrs[0],
                  actual_addrs[1], actual_addrs[2], actual_addrs[3]);
         pass_count++;
      end else begin
         $display("  FAIL: Expected 100C 1000 1004 1008");
         $display("        Got      %h %h %h %h",
                  actual_addrs[0], actual_addrs[1], actual_addrs[2], actual_addrs[3]);
      end

      // Test 3: WRAP8 with halfword transfers
      $display("Test 3: WRAP8 burst (halfword size)");
      // Start at 0x200A, boundary is 16 bytes (8 * 2)
      calc.init(32'h200A, WRAP8, HALFWORD);

      actual_addrs = new[8];
      actual_addrs[0] = calc.current_address;
      for (int i = 1; i < 8; i++) begin
         actual_addrs[i] = calc.next_address();
      end

      test_count++;
      // WRAP8 halfword: 16-byte boundary, starts at +10, wraps at +16
      // Expected: 200A, 200C, 200E, 2000, 2002, 2004, 2006, 2008
      if (actual_addrs[0] == 32'h200A && actual_addrs[3] == 32'h2000 &&
          actual_addrs[7] == 32'h2008) begin
         $display("  PASS: First=%h, wrap=%h, last=%h",
                  actual_addrs[0], actual_addrs[3], actual_addrs[7]);
         pass_count++;
      end else begin
         $display("  FAIL: Unexpected sequence");
         for (int i = 0; i < 8; i++)
            $display("        [%0d] = %h", i, actual_addrs[i]);
      end

      // Test 4: INCR8 (no wrapping)
      $display("Test 4: INCR8 burst (no wrapping)");
      calc.init(32'h3008, INCR8, WORD);

      actual_addrs = new[8];
      actual_addrs[0] = calc.current_address;
      for (int i = 1; i < 8; i++) begin
         actual_addrs[i] = calc.next_address();
      end

      test_count++;
      // INCR8 word: just increments by 4 each time
      if (actual_addrs[0] == 32'h3008 && actual_addrs[1] == 32'h300C &&
          actual_addrs[7] == 32'h3024) begin
         $display("  PASS: First=%h, second=%h, last=%h",
                  actual_addrs[0], actual_addrs[1], actual_addrs[7]);
         pass_count++;
      end else begin
         $display("  FAIL: Unexpected sequence");
      end

      // Test 5: WRAP16 with byte transfers (complex case)
      $display("Test 5: WRAP16 burst (byte size) - 16-byte boundary");
      // Start at 0x400E, boundary is 16 bytes (16 * 1)
      calc.init(32'h400E, WRAP16, BYTE);

      actual_addrs = new[16];
      actual_addrs[0] = calc.current_address;
      for (int i = 1; i < 16; i++) begin
         actual_addrs[i] = calc.next_address();
      end

      test_count++;
      // Should wrap from 400F to 4000
      if (actual_addrs[0] == 32'h400E && actual_addrs[1] == 32'h400F &&
          actual_addrs[2] == 32'h4000 && actual_addrs[15] == 32'h400D) begin
         $display("  PASS: Start=%h, before_wrap=%h, after_wrap=%h, last=%h",
                  actual_addrs[0], actual_addrs[1], actual_addrs[2], actual_addrs[15]);
         pass_count++;
      end else begin
         $display("  FAIL: Unexpected sequence");
         for (int i = 0; i < 16; i++)
            $display("        [%0d] = %h", i, actual_addrs[i]);
      end

      // Test 6: Edge case - start exactly at boundary
      $display("Test 6: WRAP4 starting at boundary");
      calc.init(32'h5000, WRAP4, WORD);

      actual_addrs = new[4];
      actual_addrs[0] = calc.current_address;
      for (int i = 1; i < 4; i++) begin
         actual_addrs[i] = calc.next_address();
      end

      test_count++;
      // Should be sequential: 5000, 5004, 5008, 500C
      if (actual_addrs[0] == 32'h5000 && actual_addrs[1] == 32'h5004 &&
          actual_addrs[2] == 32'h5008 && actual_addrs[3] == 32'h500C) begin
         $display("  PASS: %h %h %h %h (no wrap needed)",
                  actual_addrs[0], actual_addrs[1], actual_addrs[2], actual_addrs[3]);
         pass_count++;
      end else begin
         $display("  FAIL: Unexpected sequence");
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
