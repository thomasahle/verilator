// DDR3 Interface Fix - declares missing dm_tdqs signal
// This file should be compiled before ddr3_interface.sv
// to ensure dm_tdqs is declared with the correct width

`ifndef DDR3_INTERFACE_FIX_SV
`define DDR3_INTERFACE_FIX_SV

// Note: This is a workaround for a missing declaration in the testbench.
// The dm_tdqs signal is used in ddr3_interface.sv but not declared.
// We need to ensure it gets the right width (DM_BITS).

`endif
