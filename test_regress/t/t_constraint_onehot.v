// DESCRIPTION: Verilator: Verilog Test module
//
// Test $onehot and $onehot0 in constraints (IEEE 1800-2017 18.5.9)

/* verilator lint_off WIDTHTRUNC */

module t(/*AUTOARG*/);

   class Cls;
      rand bit [7:0] m_onehot;
      rand bit [7:0] m_onehot0;
      rand bit [3:0] m_small;

      // $onehot - exactly one bit set
      constraint c_onehot { $onehot(m_onehot) == 1; }

      // $onehot0 - at most one bit set (zero or one)
      constraint c_onehot0 { $onehot0(m_onehot0) == 1; }

      // Combined constraint
      constraint c_small { $onehot(m_small); }
   endclass

   initial begin
      Cls c;
      int pass_count = 0;
      int onehot_ones = 0;
      int onehot0_ones = 0;

      c = new;

      // Run multiple randomizations
      for (int i = 0; i < 20; i++) begin
         if (!c.randomize()) $stop;

         // Check $onehot constraint - exactly one bit set
         onehot_ones = $countones(c.m_onehot);
         if (onehot_ones != 1) begin
            $display("ERROR: m_onehot=%b has %0d bits set, expected 1", c.m_onehot, onehot_ones);
            $stop;
         end

         // Check $onehot0 constraint - zero or one bit set
         onehot0_ones = $countones(c.m_onehot0);
         if (onehot0_ones > 1) begin
            $display("ERROR: m_onehot0=%b has %0d bits set, expected 0 or 1", c.m_onehot0, onehot0_ones);
            $stop;
         end

         // Check m_small constraint
         if (!$onehot(c.m_small)) begin
            $display("ERROR: m_small=%b is not onehot", c.m_small);
            $stop;
         end

         pass_count++;
      end

      $display("All %0d randomizations passed!", pass_count);
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
