// DESCRIPTION: Verilator: Test basic timing delays work
module t;
  bit reset_n;

  initial begin
    $display("[%0t] Starting", $time);
    reset_n = 1;
    $display("[%0t] reset_n = 1", $time);
    #15;
    $display("[%0t] After #15", $time);
    reset_n = 0;
    $display("[%0t] reset_n = 0", $time);
    #10;
    $display("[%0t] After #10", $time);
    reset_n = 1;
    $display("[%0t] reset_n = 1 again", $time);
    #5;
    $display("*-* All Finished *-*");
    $finish;
  end
endmodule
