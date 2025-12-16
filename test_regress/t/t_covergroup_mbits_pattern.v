// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test covergroup patterns similar to mbits-mirafra UVM VIPs
// Uses module-level variables since class-embedded covergroups with
// enclosing scope access are not yet supported

module t;
   // Module-level sampling variables
   bit [7:0] data;
   bit [2:0] dataType;
   bit [1:0] parityType;
   bit stopBit;
   bit hasParity;

   // Covergroup at module level - mbits-like patterns
   covergroup TxCovergroup;
      // Data coverpoint
      TX_CP: coverpoint data {
         bins low = {[0:127]};
         bins high = {[128:255]};
      }

      // Data pattern coverpoint
      DATA_PATTERN_8: coverpoint data {
         bins pattern_all_1 = {8'b11111111};
         bins pattern_alt_10 = {8'b10101010};
         bins pattern_high = {8'b11110000};
         bins pattern_all_0 = {8'b00000000};
         bins pattern_alt_01 = {8'b01010101};
      }

      // Config coverpoints
      DATA_WIDTH_CP: coverpoint dataType {
         bins FIVE_BIT = {0};
         bins SIX_BIT = {1};
         bins SEVEN_BIT = {2};
         bins EIGHT_BIT = {3};
      }

      PARITY_CP: coverpoint parityType {
         bins EVEN_PARITY = {0};
         bins ODD_PARITY = {1};
      }

      STOP_BIT_CP: coverpoint stopBit {
         bins ONE_BIT = {0};
         bins TWO_BIT = {1};
      }

      HAS_PARITY_CP: coverpoint hasParity {
         bins PARITY_DISABLED = {0};
         bins PARITY_ENABLED = {1};
      }

      // Cross coverage (parsed but not yet implemented - nodes deleted)
      DATA_WIDTH_PARITY: cross DATA_WIDTH_CP, PARITY_CP;
      DATA_WIDTH_STOP: cross DATA_WIDTH_CP, STOP_BIT_CP;
   endgroup

   TxCovergroup cg;
   real coverage_pct;

   initial begin
      cg = new;

      // Sample some data patterns
      dataType = 3;  // 8-bit
      parityType = 0;  // Even
      stopBit = 0;  // 1 bit
      hasParity = 1;  // Enabled

      // Sample low data
      data = 64;
      cg.sample();

      coverage_pct = cg.get_inst_coverage();
      $display("After sampling low: %0.2f%%", coverage_pct);

      // Sample high data
      data = 200;
      cg.sample();

      coverage_pct = cg.get_inst_coverage();
      $display("After sampling high: %0.2f%%", coverage_pct);

      // Sample specific patterns
      data = 8'b11111111;
      cg.sample();

      data = 8'b10101010;
      cg.sample();

      coverage_pct = cg.get_inst_coverage();
      $display("After sampling patterns: %0.2f%%", coverage_pct);

      // Vary config
      dataType = 2;  // 7-bit
      parityType = 1;  // Odd
      data = 100;
      cg.sample();

      coverage_pct = cg.get_inst_coverage();
      $display("After varying config: %0.2f%%", coverage_pct);

      if (coverage_pct > 0.0) begin
         $write("*-* All Finished *-*\n");
      end else begin
         $display("ERROR: Expected non-zero coverage");
      end
      $finish;
   end
endmodule
