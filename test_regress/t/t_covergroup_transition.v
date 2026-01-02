// DESCRIPTION: Verilator: Verilog Test module for transition coverage
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test transition coverage (=>) in covergroups

module t (/*AUTOARG*/);

   // Simple covergroup with transition bins
   covergroup cg;
      cp_value: coverpoint value {
         bins rising = (0 => 1);           // Two-step transition
         bins triple = (0 => 1 => 2);      // Three-step transition
         bins multi = (1 => 2 => 3 => 4);  // Four-step transition
      }
   endgroup

   cg m_cg;
   int value;

   initial begin
      m_cg = new;

      // Check initial coverage (should be 0%)
      $display("Initial coverage: %.1f%%", m_cg.get_inst_coverage());
      if (m_cg.get_inst_coverage() != 0.0) $stop;

      // Sample sequence: 0, 1 - should hit 'rising' bin (0 => 1)
      value = 0;
      m_cg.sample();
      value = 1;
      m_cg.sample();

      $display("After (0=>1): %.1f%%", m_cg.get_inst_coverage());
      // 'rising' should be covered (1/3 bins = 33.3%)
      if (m_cg.get_inst_coverage() < 33.0 || m_cg.get_inst_coverage() > 34.0) begin
         $display("ERROR: Expected ~33.3%%, got %.1f%%", m_cg.get_inst_coverage());
         $stop;
      end

      // Sample: 0, 1, 2 - should hit 'rising' again AND 'triple' bin
      value = 0;
      m_cg.sample();
      value = 1;
      m_cg.sample();
      value = 2;
      m_cg.sample();

      $display("After (0=>1=>2): %.1f%%", m_cg.get_inst_coverage());
      // 'rising' and 'triple' should be covered (2/3 bins = 66.7%)
      if (m_cg.get_inst_coverage() < 66.0 || m_cg.get_inst_coverage() > 67.0) begin
         $display("ERROR: Expected ~66.7%%, got %.1f%%", m_cg.get_inst_coverage());
         $stop;
      end

      // Sample: 1, 2, 3, 4 - should hit 'multi' bin
      value = 1;
      m_cg.sample();
      value = 2;
      m_cg.sample();
      value = 3;
      m_cg.sample();
      value = 4;
      m_cg.sample();

      $display("After (1=>2=>3=>4): %.1f%%", m_cg.get_inst_coverage());
      // All bins should be covered (3/3 = 100%)
      if (m_cg.get_inst_coverage() != 100.0) begin
         $display("ERROR: Expected 100.0%%, got %.1f%%", m_cg.get_inst_coverage());
         $stop;
      end

      $display("*-* All Coverage Tests Passed *-*");
      $write("*-* All Coverage Tests Passed *-*\n");
      $finish;
   end

endmodule
