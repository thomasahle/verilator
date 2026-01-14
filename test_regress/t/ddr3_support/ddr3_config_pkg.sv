`ifndef DDR3_CONFIG_PKG_SV
`define DDR3_CONFIG_PKG_SV

// ============================================================================
// DDR3 Configuration Package - Stub for Verilator compilation
// ============================================================================
// This package provides configuration types used by the DDR3 UVM testbench.
// It's a stub package created for Verilator compatibility.
// ============================================================================

package ddr3_config_pkg;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // Additional command enum values not defined in ddr3_transactions_pkg
  // The monitor uses these but they're missing from the base definitions
  typedef enum {
    CMD_MRW,    // Mode Register Write (alias for CMD_MRS in monitor context)
    CMD_ZQC     // ZQ Calibration (generic, covers ZQCL/ZQCS)
  } cmd_ext_t;

  // Configuration class for DDR3 agent
  class ddr3_config extends uvm_object;
    `uvm_object_utils(ddr3_config)

    // Agent mode: active or passive
    uvm_active_passive_enum is_active = UVM_ACTIVE;

    // Enable coverage collection
    bit coverage_enable = 0;

    // Enable checks
    bit checks_enable = 1;

    function new(string name = "ddr3_config");
      super.new(name);
    endfunction
  endclass

endpackage : ddr3_config_pkg

`endif
