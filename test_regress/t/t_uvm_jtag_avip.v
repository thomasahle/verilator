// DESCRIPTION: Verilator: Test JTAG AVIP
// Wrapper module that instantiates JtagHdlTop and JtagHvlTop
module tb_top;
  JtagHdlTop hdl();
  JtagHvlTop hvl();
endmodule
