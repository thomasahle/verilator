`ifndef DDR3_TIMINGS_PKG_SV
`define DDR3_TIMINGS_PKG_SV

// ============================================================================
// DDR3 Timings Package - Stub for Verilator compilation
// ============================================================================
// This package provides timing parameters used by the DDR3 UVM testbench.
// It's a stub package created for Verilator compatibility.
// ============================================================================

package ddr3_timings_pkg;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // Timing parameters - these would typically come from a specific speed grade
  // Values here are representative for DDR3-1600

  // Clock period in ps
  parameter real T_CK = 1250.0;  // 800 MHz

  // Core timing parameters (in ps)
  parameter int T_RCD = 13750;   // RAS to CAS delay
  parameter int T_RP = 13750;    // Row precharge time
  parameter int T_RC = 48750;    // Row cycle time
  parameter int T_RAS = 35000;   // Row active time
  parameter int T_WR = 15000;    // Write recovery time
  parameter int T_RTP = 7500;    // Read to precharge
  parameter int T_WTR = 7500;    // Write to read delay
  parameter int T_CCD = 5000;    // CAS to CAS delay
  parameter int T_FAW = 40000;   // Four activate window
  parameter int T_RRD = 6000;    // Row to row delay
  parameter int T_RFC = 350000;  // Refresh to active
  parameter int T_REFI = 7800000; // Refresh interval

  // Mode register timings
  parameter int T_MOD = 15000;   // Mode register set delay
  parameter int T_MRD = 4;       // Mode register delay (cycles)

  // ZQ calibration timings
  parameter int T_ZQINIT = 640000; // ZQ initial calibration
  parameter int T_ZQOPER = 320000; // ZQ long calibration
  parameter int T_ZQCS = 64000;   // ZQ short calibration

  // Power-up timings
  parameter int T_XPR = 360000;  // Exit reset to any command

endpackage : ddr3_timings_pkg

`endif
