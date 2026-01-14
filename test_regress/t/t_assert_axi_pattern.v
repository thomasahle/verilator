// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test for AXI-style SVA patterns combining throughout and goto repetition
// Pattern: $stable(valid) throughout ready[->1]
// Meaning: valid must remain stable until ready goes high

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   int   cyc = 0;
   logic aresetn;
   logic arvalid, arready;
   logic [31:0] araddr;
   logic [2:0] arprot;

   // AXI4-Lite pattern: stable signals throughout handshake
   // arvalidIsHighThenInformationStableUntilTransferOccur
   property p_valid_stable_until_ready;
      @(posedge clk) disable iff (!aresetn)
      ($rose(arvalid) && !arready) |=> (($stable(arvalid) && $stable(araddr) && $stable(arprot)) throughout arready[->1]);
   endproperty

   // Simpler test: stable value throughout handshake
   property p_stable_throughout_goto;
      @(posedge clk) disable iff (!aresetn)
      ($rose(arvalid) && !arready) |=> ($stable(araddr) throughout arready[->1]);
   endproperty

   assert property (p_valid_stable_until_ready)
      else $error("p_valid_stable_until_ready failed at cyc=%0d", cyc);

   assert property (p_stable_throughout_goto)
      else $error("p_stable_throughout_goto failed at cyc=%0d", cyc);

   always @(posedge clk) begin
      cyc <= cyc + 1;

      // Test pattern: valid rises, stays stable, then ready comes
      case (cyc)
         0: begin aresetn <= 0; arvalid <= 0; arready <= 0; araddr <= 32'hA; arprot <= 3'b0; end
         1: begin aresetn <= 1; arvalid <= 0; arready <= 0; araddr <= 32'hA; arprot <= 3'b0; end
         2: begin arvalid <= 0; arready <= 0; end
         3: begin arvalid <= 1; arready <= 0; araddr <= 32'h100; arprot <= 3'b001; end  // valid rises
         4: begin arvalid <= 1; arready <= 0; araddr <= 32'h100; arprot <= 3'b001; end  // stable
         5: begin arvalid <= 1; arready <= 1; araddr <= 32'h100; arprot <= 3'b001; end  // ready arrives
         6: begin arvalid <= 0; arready <= 0; araddr <= 32'h200; arprot <= 3'b010; end
         7: begin arvalid <= 1; arready <= 1; araddr <= 32'h300; arprot <= 3'b011; end  // immediate handshake
         8: begin arvalid <= 0; arready <= 0; end
         10: begin
            $write("*-* All Coverage *-*\n");
            $finish;
         end
         default: begin end
      endcase
   end

endmodule
