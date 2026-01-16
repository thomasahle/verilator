// DESCRIPTION: Verilator: Test cross coverage with function declaration

module t;
  int a;
  int b;

  /* verilator lint_off UNSIGNED */
  /* verilator lint_off CMPCONST */
  covergroup cg with function sample (int aa, int bb);
    cp_a: coverpoint aa;
    cp_b: coverpoint bb;
    cross cp_a, cp_b {
      function void sample(int x, int y);
      endfunction
    }
  endgroup
  /* verilator lint_on CMPCONST */
  /* verilator lint_on UNSIGNED */

  cg cg_i = new();

  initial begin
    a = 0;
    b = 0;
    repeat (3) begin
      #1;
      a = a + 1;
      b = b + 2;
      cg_i.sample(a, b);
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
