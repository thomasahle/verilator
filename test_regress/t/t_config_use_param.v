// DESCRIPTION: Verilator: Test config use parameter assignment

module cell_mod #(parameter int WIDTH = 1) ();
endmodule

module top;
  cell_mod #(.WIDTH(4)) u0();
  cell_mod u1();
endmodule

config cfg;
  design work.top;
  default liblist work;
  instance top.u1 use work.cell_mod #(.WIDTH(8));
endconfig
