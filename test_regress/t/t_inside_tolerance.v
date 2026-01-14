// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test tolerance ranges in inside operator: [center +/- tol] and [center +%- pct]

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;
  real r;
  int i;

  initial begin
    // Test with real values using absolute tolerance (+/-)
    // r=1492.4 should be:
    //   inside [1492-2:1492+2] = [1490:1494] -> yes (1)
    //   inside [1492-1:1492+1] = [1491:1493] -> yes (1)
    //   inside [1482-2:1482+2] = [1480:1484] -> no (0)
    //   inside [1494-1:1494+1] = [1493:1495] -> no (0)
    r = 1492.4;
    `checkh(r inside {[1492 +/- 2]}, 1'b1);
    `checkh(r inside {[1492 +/- 1]}, 1'b1);
    `checkh(r inside {[1482 +/- 2]}, 1'b0);
    `checkh(r inside {[1494 +/- 1]}, 1'b0);

    // Test with real values using percentage tolerance (+%-)
    // r=100.0 should be:
    //   inside [100*(1-0.1):100*(1+0.1)] = [90:110] -> yes (1)
    //   inside [100*(1-0.05):100*(1+0.05)] = [95:105] -> yes (1)
    r = 100.0;
    `checkh(r inside {[100 +%- 10]}, 1'b1);
    `checkh(r inside {[100 +%- 5]}, 1'b1);
    // r=150.0 should be:
    //   inside [100*0.5:100*1.5] = [50:150] -> yes (1)
    //   inside [100*0.51:100*1.49] = [51:149] -> no (0)
    r = 150.0;
    `checkh(r inside {[100 +%- 50]}, 1'b1);
    `checkh(r inside {[100 +%- 49]}, 1'b0);

    // Test with integer values using absolute tolerance
    // i=50 should be:
    //   inside [50-5:50+5] = [45:55] -> yes (1)
    //   inside [50-0:50+0] = [50:50] -> yes (1)
    //   inside [45-5:45+5] = [40:50] -> yes (1)
    //   inside [44-5:44+5] = [39:49] -> no (0)
    i = 50;
    `checkh(i inside {[50 +/- 5]}, 1'b1);
    `checkh(i inside {[50 +/- 0]}, 1'b1);
    `checkh(i inside {[45 +/- 5]}, 1'b1);
    `checkh(i inside {[44 +/- 5]}, 1'b0);

    // Test with integer values using percentage tolerance
    // For +%- with integers, we use integer arithmetic
    // i=100 inside [100*0.9:100*1.1] = [90:110] -> yes (1)
    // i=90 inside [100*0.9:100*1.1] = [90:110] -> yes (1)
    // i=110 inside [100*0.9:100*1.1] = [90:110] -> yes (1)
    // i=89 inside [100*0.9:100*1.1] = [90:110] -> no (0)
    i = 100;
    `checkh(i inside {[100 +%- 10]}, 1'b1);
    i = 90;
    `checkh(i inside {[100 +%- 10]}, 1'b1);
    i = 110;
    `checkh(i inside {[100 +%- 10]}, 1'b1);
    i = 89;
    `checkh(i inside {[100 +%- 10]}, 1'b0);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
