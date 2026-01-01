// DESCRIPTION: Verilator: Test AXI4-Lite AVIP
// Wrapper module that instantiates Axi4LiteHdlTop and Axi4LiteHvlTop
module tb_top;
  Axi4LiteHdlTop hdl();
  Axi4LiteHvlTop hvl();
endmodule
