// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test covergroup static get_coverage() method
// IEEE 1800-2017 19.3.1 - get_coverage() returns aggregated type-level coverage

module t;
   bit [1:0] val;

   covergroup cg;
      VAL_CP: coverpoint val {
         bins zero = {0};
         bins one = {1};
         bins two = {2};
         bins three = {3};
      }
   endgroup

   cg cg_inst1;
   cg cg_inst2;
   real type_cov, inst1_cov, inst2_cov;

   initial begin
      cg_inst1 = new;
      cg_inst2 = new;

      // Before sampling - 0%
      type_cov = cg::get_coverage();
      $display("Type coverage before sampling: %0.2f%%", type_cov);
      if (type_cov != 0.0) begin
         $display("ERROR: Expected 0.0%%, got %0.2f%%", type_cov);
         $stop;
      end

      // Sample val=0 on instance 1
      // Type coverage: 1 of 4 bins = 25%
      val = 0;
      cg_inst1.sample();

      type_cov = cg::get_coverage();
      inst1_cov = cg_inst1.get_inst_coverage();
      $display("After inst1 sample val=0:");
      $display("  Type coverage: %0.2f%%", type_cov);
      $display("  Instance 1 coverage: %0.2f%%", inst1_cov);

      if (type_cov != 25.0) begin
         $display("ERROR: Expected type cov 25.0%%, got %0.2f%%", type_cov);
         $stop;
      end
      if (inst1_cov != 25.0) begin
         $display("ERROR: Expected inst1 cov 25.0%%, got %0.2f%%", inst1_cov);
         $stop;
      end

      // Sample val=1 on instance 2 (different bin than instance 1)
      // Type coverage: 2 of 4 bins = 50% (aggregated across both instances)
      // Instance 2 coverage: 1 of 4 bins = 25%
      val = 1;
      cg_inst2.sample();

      type_cov = cg::get_coverage();
      inst1_cov = cg_inst1.get_inst_coverage();
      inst2_cov = cg_inst2.get_inst_coverage();
      $display("After inst2 sample val=1:");
      $display("  Type coverage: %0.2f%%", type_cov);
      $display("  Instance 1 coverage: %0.2f%%", inst1_cov);
      $display("  Instance 2 coverage: %0.2f%%", inst2_cov);

      if (type_cov != 50.0) begin
         $display("ERROR: Expected type cov 50.0%%, got %0.2f%%", type_cov);
         $stop;
      end
      // Instance 1 still at 25% (only sampled val=0)
      if (inst1_cov != 25.0) begin
         $display("ERROR: Expected inst1 cov 25.0%%, got %0.2f%%", inst1_cov);
         $stop;
      end
      // Instance 2 at 25% (only sampled val=1)
      if (inst2_cov != 25.0) begin
         $display("ERROR: Expected inst2 cov 25.0%%, got %0.2f%%", inst2_cov);
         $stop;
      end

      // Sample val=2 on instance 1
      // Type coverage: 3 of 4 bins = 75%
      val = 2;
      cg_inst1.sample();

      type_cov = cg::get_coverage();
      inst1_cov = cg_inst1.get_inst_coverage();
      $display("After inst1 sample val=2:");
      $display("  Type coverage: %0.2f%%", type_cov);
      $display("  Instance 1 coverage: %0.2f%%", inst1_cov);

      if (type_cov != 75.0) begin
         $display("ERROR: Expected type cov 75.0%%, got %0.2f%%", type_cov);
         $stop;
      end
      // Instance 1 now at 50% (sampled val=0 and val=2)
      if (inst1_cov != 50.0) begin
         $display("ERROR: Expected inst1 cov 50.0%%, got %0.2f%%", inst1_cov);
         $stop;
      end

      // Sample val=3 on instance 2
      // Type coverage: 4 of 4 bins = 100%
      val = 3;
      cg_inst2.sample();

      type_cov = cg::get_coverage();
      inst2_cov = cg_inst2.get_inst_coverage();
      $display("After inst2 sample val=3:");
      $display("  Type coverage: %0.2f%%", type_cov);
      $display("  Instance 2 coverage: %0.2f%%", inst2_cov);

      if (type_cov != 100.0) begin
         $display("ERROR: Expected type cov 100.0%%, got %0.2f%%", type_cov);
         $stop;
      end
      // Instance 2 now at 50% (sampled val=1 and val=3)
      if (inst2_cov != 50.0) begin
         $display("ERROR: Expected inst2 cov 50.0%%, got %0.2f%%", inst2_cov);
         $stop;
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
