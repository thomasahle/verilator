// DESCRIPTION: Verilator: Test reserved address range constraints using enums
// This pattern is used in protocol verification (I3C, etc.) where certain
// address ranges are reserved and must be excluded from randomization
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
   // Reserved address groups (like I3C Group 0: 0000_XXX and Group 1: 1111_XXX)
   typedef enum bit [6:0] {
      GRP0_RSVD0 = 7'b0000_000,
      GRP0_RSVD1 = 7'b0000_001,
      GRP0_RSVD2 = 7'b0000_010,
      GRP0_RSVD3 = 7'b0000_011,
      GRP0_RSVD4 = 7'b0000_100,
      GRP0_RSVD5 = 7'b0000_101,
      GRP0_RSVD6 = 7'b0000_110,
      GRP0_RSVD7 = 7'b0000_111
   } group0_reserved_e;

   typedef enum bit [6:0] {
      GRP1_RSVD0 = 7'b1111_000,
      GRP1_RSVD1 = 7'b1111_001,
      GRP1_RSVD2 = 7'b1111_010,
      GRP1_RSVD3 = 7'b1111_011,
      GRP1_RSVD4 = 7'b1111_100,
      GRP1_RSVD5 = 7'b1111_101,
      GRP1_RSVD6 = 7'b1111_110,
      GRP1_RSVD7 = 7'b1111_111
   } group1_reserved_e;

   // Class with reserved address constraint
   class protocol_tx;
      rand bit [6:0] target_address;
      rand bit [7:0] data;

      // Exclude Group 0 reserved addresses (0-7)
      constraint reserved_group0_c {
         !(target_address inside {[GRP0_RSVD0 : GRP0_RSVD7]});
      }

      // Exclude Group 1 reserved addresses (120-127)
      constraint reserved_group1_c {
         !(target_address inside {[GRP1_RSVD0 : GRP1_RSVD7]});
      }

      function new();
      endfunction

      function bit is_reserved();
         return (target_address <= 7 || target_address >= 120);
      endfunction
   endclass

   // Class with valid range constraint (alternative approach)
   class protocol_tx_v2;
      rand bit [6:0] target_address;

      // Constrain to valid addresses only (8-119)
      constraint valid_address_c {
         target_address inside {[8:119]};
      }

      function new();
      endfunction
   endclass

   initial begin
      protocol_tx tx1;
      protocol_tx_v2 tx2;
      int reserved_count;
      int valid_count;
      int test_iterations;

      test_iterations = 100;

      // Test 1: Verify reserved addresses are excluded (negative constraint)
      $display("Test 1: Reserved address exclusion constraint");
      tx1 = new();
      reserved_count = 0;
      valid_count = 0;

      for (int i = 0; i < test_iterations; i++) begin
         if (tx1.randomize()) begin
            if (tx1.is_reserved()) begin
               reserved_count++;
               $display("ERROR: Got reserved address %0d", tx1.target_address);
            end else begin
               valid_count++;
            end
         end else begin
            $display("ERROR: Randomization failed");
         end
      end

      if (reserved_count == 0 && valid_count == test_iterations) begin
         $display("  PASS: All %0d addresses were valid (8-119)", valid_count);
      end else begin
         $display("  FAIL: Got %0d reserved addresses", reserved_count);
         $stop;
      end

      // Test 2: Verify positive constraint approach
      $display("Test 2: Valid address range constraint");
      tx2 = new();
      reserved_count = 0;
      valid_count = 0;

      for (int i = 0; i < test_iterations; i++) begin
         if (tx2.randomize()) begin
            if (tx2.target_address < 8 || tx2.target_address > 119) begin
               reserved_count++;
               $display("ERROR: Got out-of-range address %0d", tx2.target_address);
            end else begin
               valid_count++;
            end
         end else begin
            $display("ERROR: Randomization failed");
         end
      end

      if (reserved_count == 0 && valid_count == test_iterations) begin
         $display("  PASS: All %0d addresses in range (8-119)", valid_count);
      end else begin
         $display("  FAIL: Got %0d out-of-range addresses", reserved_count);
         $stop;
      end

      // Test 3: Verify distribution across valid range
      $display("Test 3: Distribution check");
      begin
         int addr_seen[128];
         int unique_addrs;

         foreach (addr_seen[i]) addr_seen[i] = 0;

         for (int i = 0; i < 500; i++) begin
            void'(tx1.randomize());
            addr_seen[tx1.target_address]++;
         end

         unique_addrs = 0;
         for (int i = 8; i < 120; i++) begin
            if (addr_seen[i] > 0) unique_addrs++;
         end

         // Should see reasonable coverage of the 112 valid addresses
         if (unique_addrs > 50) begin
            $display("  PASS: Saw %0d unique addresses (good distribution)", unique_addrs);
         end else begin
            $display("  WARN: Only saw %0d unique addresses (poor distribution)", unique_addrs);
         end
      end

      $display("*-* All Finished *-*");
      $finish;
   end

endmodule
