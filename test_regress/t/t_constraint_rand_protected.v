// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test for rand protected class members
// Pattern from SPI AVIP: rand protected bit[2:0] primaryPrescalar

module t;

   class Config;
      // Public rand field
      rand bit [7:0] public_val;

      // Protected rand field (accessible in derived classes)
      rand protected bit [2:0] prescalar;
      rand protected bit [3:0] divider;

      // Constraints on protected fields
      constraint prescalar_c { prescalar inside {[1:7]}; }
      constraint divider_c { divider > 0; }

      // Method to access protected fields
      function bit [2:0] get_prescalar();
         return prescalar;
      endfunction

      function bit [3:0] get_divider();
         return divider;
      endfunction
   endclass

   class DerivedConfig extends Config;
      rand bit [7:0] derived_val;

      // Can access protected members in derived class
      constraint derived_c {
         // Derived class can reference protected members
         derived_val > {5'b0, prescalar};
         derived_val < {4'b0, divider} * 16;
      }

      function void print_all();
         $display("prescalar=%0d divider=%0d derived=%0d", prescalar, divider, derived_val);
      endfunction
   endclass

   initial begin
      Config cfg;
      DerivedConfig dcfg;
      int pass_count;

      // Test base class with protected rand fields
      cfg = new;
      pass_count = 0;
      for (int i = 0; i < 10; i++) begin
         if (cfg.randomize() == 0) $stop;
         // prescalar should be 1-7
         if (cfg.get_prescalar() >= 1 && cfg.get_prescalar() <= 7) pass_count++;
         // divider should be > 0
         if (cfg.get_divider() > 0) pass_count++;
      end
      if (pass_count != 20) begin
         $display("ERROR: Base class constraints failed, pass_count=%0d", pass_count);
         $stop;
      end
      $display("Base class protected rand: PASSED");

      // Test derived class accessing protected fields
      dcfg = new;
      pass_count = 0;
      for (int i = 0; i < 10; i++) begin
         if (dcfg.randomize() == 0) $stop;
         // derived_val should be > prescalar
         if (dcfg.derived_val > {5'b0, dcfg.get_prescalar()}) pass_count++;
      end
      if (pass_count != 10) begin
         $display("ERROR: Derived class constraints failed, pass_count=%0d", pass_count);
         $stop;
      end
      $display("Derived class protected rand access: PASSED");

      dcfg.print_all();

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
