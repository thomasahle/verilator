// DESCRIPTION: Verilator: Test SVA sequence delay patterns
// Common patterns used in UVM VIPs like AHB AVIP
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
   logic clk = 0;
   int cyc = 0;

   // Clock generator for timing mode
   always #5 clk = ~clk;
   logic hresetn;
   logic [31:0] haddr;
   logic [31:0] hwdata;
   logic [2:0] hsize;
   logic [2:0] hburst;
   logic [1:0] htrans;
   logic hwrite;
   logic hready;
   logic hresp;
   logic hselx;
   logic [3:0] hwstrb;

   int pass_count = 0;
   int fail_count = 0;

   // Pattern 1: fixed delay ##1 with sequence on LHS of implication
   // From AHB checkHwdataValid: (cond) ##1 $stable(hready) |-> (!$isunknown(hwdata))
   property p_seq_delay;
      @(posedge clk) disable iff (!hresetn)
      (hwrite && hready && htrans != 2'b00) ##1 $stable(hready) |-> (!$isunknown(hwdata));
   endproperty
   assert property (p_seq_delay) pass_count++; else fail_count++;

   // Pattern 2: ##1 in sequence on LHS with $past
   // From AHB checkBurstIncr: cond ##1 (cond) |-> expr with $past
   property p_burst_incr;
      @(posedge clk) disable iff (!hresetn)
      (hburst == 3'b011 && htrans == 2'b10) ##1 (htrans == 2'b11 && $stable(hburst))
         |-> (haddr == $past(haddr) + (1 << hsize));
   endproperty
   assert property (p_burst_incr) pass_count++; else fail_count++;

   // Pattern 3: two-cycle sequence on LHS
   // Similar to AHB checkTransIdleToNonSeq: cond ##1 cond2 |-> expr
   property p_idle_to_nonseq;
      @(posedge clk) disable iff (!hresetn)
      (htrans == 2'b00) ##1 (hselx) |-> (htrans == 2'b10);
   endproperty
   assert property (p_idle_to_nonseq) pass_count++; else fail_count++;

   // Pattern 4: $stable in sequence
   property p_stable_seq;
      @(posedge clk) disable iff (!hresetn)
      (hready) ##1 $stable(haddr) |-> 1'b1;
   endproperty
   assert property (p_stable_seq) pass_count++; else fail_count++;

   always @(posedge clk) begin
      cyc <= cyc + 1;

      // Initialize
      if (cyc == 0) begin
         hresetn <= 0;
         haddr <= 32'h0;
         hwdata <= 32'h12345678;
         hsize <= 3'b010;  // 4-byte
         hburst <= 3'b000;
         htrans <= 2'b00;
         hwrite <= 0;
         hready <= 0;
         hresp <= 0;
         hselx <= 0;
         hwstrb <= 4'b1111;
      end

      // Release reset
      if (cyc == 2) hresetn <= 1;

      // Test pattern 1: Write with stable ready
      if (cyc == 5) begin
         hwrite <= 1;
         hready <= 1;
         htrans <= 2'b10;  // NONSEQ
         hwdata <= 32'hDEADBEEF;
      end
      if (cyc == 6) begin
         // hready stable
      end
      if (cyc == 7) begin
         hwrite <= 0;
         htrans <= 2'b00;
      end

      // Test pattern 3: IDLE to NONSEQ transition
      if (cyc == 10) begin
         htrans <= 2'b00;  // IDLE
         hselx <= 0;
      end
      if (cyc == 11) begin
         hselx <= 1;
         htrans <= 2'b10;  // NONSEQ
      end

      // Test pattern 2: Burst increment
      if (cyc == 15) begin
         hburst <= 3'b011;  // INCR4
         htrans <= 2'b10;   // NONSEQ
         haddr <= 32'h100;
      end
      if (cyc == 16) begin
         htrans <= 2'b11;   // SEQ
         haddr <= 32'h104;  // Should be +4 for hsize=2
      end

      // End test
      if (cyc >= 20) begin
         $display("Pass count: %d, Fail count: %d", pass_count, fail_count);
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
