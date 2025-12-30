// DESCRIPTION: Verilator: Test covergroup iff clause on bins with sample function
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test that covergroup iff clause works on bins with sample function parameters

module t;

  class Transaction;
    int addr;
    int data;

    function new(int a = 0, int d = 0);
      addr = a;
      data = d;
    endfunction
  endclass

  class Coverage;
    // Covergroup with sample function that takes a class reference
    covergroup cg with function sample (Transaction t);
      option.per_instance = 1;

      // Basic coverpoint
      ADDR_CP: coverpoint t.addr {
        bins low_addr = { [0:255] };
        bins high_addr = { [256:1023] };
      }

      // Coverpoint with iff on the entire coverpoint
      ADDR_ALIGNED_CP: coverpoint t.addr iff (t.addr[1:0] == 2'b00) {
        bins aligned = { [0:1023] };
      }

      // Bins with iff clause - this is the pattern used in AHB AVIP
      DATA_CP: coverpoint t.data {
        bins low_data = { [0:127] };
        bins high_data = { [128:255] } iff (t.addr > 0);
        bins special = { [256:511] } iff (t.addr[0] == 0);
      }
    endgroup

    function new();
      cg = new();
    endfunction

    function void sample_trans(Transaction t);
      cg.sample(t);
    endfunction
  endclass

  initial begin
    Coverage cov = new;
    Transaction t1, t2, t3;

    // Test with various transactions
    t1 = new(0, 100);    // addr=0, data=100 (low)
    cov.sample_trans(t1);
    $display("[INFO] Sampled t1: addr=%0d, data=%0d", t1.addr, t1.data);

    t2 = new(256, 200);  // addr=256, data=200 (high, addr>0 so iff true)
    cov.sample_trans(t2);
    $display("[INFO] Sampled t2: addr=%0d, data=%0d", t2.addr, t2.data);

    t3 = new(512, 300);  // addr=512 (even), data=300 (special range, addr[0]==0 so iff true)
    cov.sample_trans(t3);
    $display("[INFO] Sampled t3: addr=%0d, data=%0d", t3.addr, t3.data);

    $display("[PASS] All samples completed without crash");
    $display("*-* All Coverage Tests Passed *-*");
    $finish;
  end
endmodule
