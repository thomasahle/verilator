// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test covergroup patterns used in mbits-mirafra VIPs
// Using simple module-level variables (no sample function arguments)

module t;
   // Config-like enums
   typedef enum {FIVE_BIT, SIX_BIT, SEVEN_BIT, EIGHT_BIT} data_type_e;
   typedef enum {EVEN_PARITY, ODD_PARITY} parity_type_e;
   typedef enum {ONE_BIT, TWO_BIT} stop_bit_e;

   // Module-level variables for sampling
   bit [7:0] tx_data;
   data_type_e dataType;
   parity_type_e parityType;
   stop_bit_e stopBit;
   bit hasParity;

   // Simple covergroup referencing module variables
   covergroup tx_covergroup;
      // Data coverpoint
      TX_CP: coverpoint tx_data {
         bins tx_data_bins = {[0:255]};
      }

      // Data width coverpoint
      DATA_WIDTH_CP: coverpoint dataType {
         bins TRANSFER_BIT_5 = {FIVE_BIT};
         bins TRANSFER_BIT_6 = {SIX_BIT};
         bins TRANSFER_BIT_7 = {SEVEN_BIT};
         bins TRANSFER_BIT_8 = {EIGHT_BIT};
      }

      // Parity coverpoint
      PARITY_CP: coverpoint parityType {
         bins PARITY_EVEN = {EVEN_PARITY};
         bins PARITY_ODD = {ODD_PARITY};
      }

      // Stop bit coverpoint
      STOP_BIT_CP: coverpoint stopBit {
         bins STOP_BIT_1 = {ONE_BIT};
         bins STOP_BIT_2 = {TWO_BIT};
      }

      // Data patterns for 8-bit mode
      DATA_PATTERN_8: coverpoint tx_data {
         bins pattern1_8 = {8'b11111111};
         bins pattern2_8 = {8'b10101010};
         bins pattern3_8 = {8'b11110000};
         bins pattern4_8 = {8'b00000000};
         bins pattern5_8 = {8'b01010101};
      }

      // Cross coverage - disabled for now (needs implementation)
      // DATA_WIDTH_CP_PARITY_CP: cross DATA_WIDTH_CP, PARITY_CP;
      // DATA_WIDTH_CP_STOP_BIT_CP: cross DATA_WIDTH_CP, STOP_BIT_CP;
   endgroup

   tx_covergroup cg;

   initial begin
      cg = new;

      // Test various configurations
      dataType = EIGHT_BIT;
      parityType = EVEN_PARITY;
      stopBit = ONE_BIT;
      hasParity = 1;

      // Sample with different data patterns
      tx_data = 8'hAA;
      cg.sample();

      tx_data = 8'hFF;
      cg.sample();

      parityType = ODD_PARITY;
      tx_data = 8'h00;
      cg.sample();

      dataType = FIVE_BIT;
      stopBit = TWO_BIT;
      tx_data = 8'h55;
      cg.sample();

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
