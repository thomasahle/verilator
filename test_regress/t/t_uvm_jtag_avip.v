// DESCRIPTION: Verilator: Test JTAG AVIP
// Wrapper module that instantiates HdlTop and HvlTop
module tb_top;
  HdlTop hdl();
  HvlTop hvl();
endmodule
