// DESCRIPTION: Verilator: Verilog Test module
//
// Test unbounded ($) in distribution constraints
// IEEE 1800-2017 18.5.4

module t;

   class Packet;
      rand int delay;
      rand int size;

      // Unbounded upper bound in dist constraint
      constraint delay_c { delay dist {[1:10]:=90, [11:$]:/10}; }
      constraint size_c { size dist {[0:100]:=50, [101:$]:/50}; }
      // Make sure values stay positive
      constraint pos_c { delay > 0; size >= 0; }
   endclass

   initial begin
      Packet p;
      int success;
      p = new();

      // Randomize and check constraints are satisfied
      repeat (10) begin
         success = p.randomize();
         if (success == 0) $stop;
         // The unbounded constraint should allow any value >= the lower bound
         if (p.delay < 1) $stop;
         if (p.size < 0) $stop;
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
