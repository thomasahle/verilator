// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Thomas Ahle.
// SPDX-License-Identifier: CC0-1.0

// Test power expressions in constraints (2**n transformed to 1<<n)

class Packet;
   rand bit [3:0] size;
   rand bit [15:0] data_width;

   // Test 2**size constraint (common AXI pattern)
   constraint size_c {
      size inside {[0:3]};  // Keep small for simpler testing
   }

   constraint width_c {
      // 2**size should equal data_width
      data_width == 2**size;
   }
endclass

module t;
   Packet pkt;
   int pass_count = 0;

   initial begin
      pkt = new;

      // Test several randomizations
      repeat(5) begin
         if (pkt.randomize()) begin
            $display("size=%0d, data_width=%0d, expected=%0d",
                     pkt.size, pkt.data_width, (1 << pkt.size));
            // Verify 2**size == data_width
            if (pkt.data_width == (1 << pkt.size)) begin
               pass_count++;
            end else begin
               $display("  MISMATCH!");
            end
         end else begin
            $display("randomize() failed");
         end
      end

      if (pass_count == 5) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end else begin
         $error("Only %0d/5 randomizations passed constraints", pass_count);
         $stop;
      end
   end
endmodule
