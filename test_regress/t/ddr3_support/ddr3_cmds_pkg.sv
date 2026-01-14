`ifndef DDR3_CMDS_PKG_SV
`define DDR3_CMDS_PKG_SV

// ============================================================================
// DDR3 Commands Package - Stub for Verilator compilation
// ============================================================================
// This package provides command-specific sequence item classes used by the
// DDR3 monitor for capturing and reporting different DDR3 commands.
// ============================================================================

package ddr3_cmds_pkg;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // Base class for all command sequence items
  class ddr3_cmd_seq_item extends uvm_sequence_item;
    `uvm_object_utils(ddr3_cmd_seq_item)

    time timestamp;

    function new(string name = "ddr3_cmd_seq_item");
      super.new(name);
    endfunction
  endclass

  // Read data item - used to capture read data from memory
  class ddr3_read_data_item extends uvm_sequence_item;
    `uvm_object_utils(ddr3_read_data_item)

    logic [63:0] data;      // Read data (assuming x8 width, 8 beats)
    time timestamp;
    int burst_id;
    int burst_beat;

    function new(string name = "ddr3_read_data_item");
      super.new(name);
      data = 0;
      timestamp = 0;
      burst_id = 0;
      burst_beat = 0;
    endfunction
  endclass

  // Activate command item
  class ddr3_act_seq_item extends ddr3_cmd_seq_item;
    `uvm_object_utils(ddr3_act_seq_item)

    logic [2:0] bank;
    logic [15:0] row;

    function new(string name = "ddr3_act_seq_item");
      super.new(name);
    endfunction
  endclass

  // Read command item
  class ddr3_rd_seq_item extends ddr3_cmd_seq_item;
    `uvm_object_utils(ddr3_rd_seq_item)

    logic [2:0] bank;
    logic [9:0] col;
    bit ap;  // auto-precharge

    function new(string name = "ddr3_rd_seq_item");
      super.new(name);
    endfunction
  endclass

  // Write command item
  class ddr3_wr_seq_item extends ddr3_cmd_seq_item;
    `uvm_object_utils(ddr3_wr_seq_item)

    logic [2:0] bank;
    logic [9:0] col;
    bit ap;  // auto-precharge

    function new(string name = "ddr3_wr_seq_item");
      super.new(name);
    endfunction
  endclass

  // Precharge command item
  class ddr3_pre_seq_item extends ddr3_cmd_seq_item;
    `uvm_object_utils(ddr3_pre_seq_item)

    logic [2:0] bank;

    function new(string name = "ddr3_pre_seq_item");
      super.new(name);
    endfunction
  endclass

  // Precharge All command item
  class ddr3_prea_seq_item extends ddr3_cmd_seq_item;
    `uvm_object_utils(ddr3_prea_seq_item)

    function new(string name = "ddr3_prea_seq_item");
      super.new(name);
    endfunction
  endclass

  // Refresh command item
  class ddr3_ref_seq_item extends ddr3_cmd_seq_item;
    `uvm_object_utils(ddr3_ref_seq_item)

    function new(string name = "ddr3_ref_seq_item");
      super.new(name);
    endfunction
  endclass

  // Mode Register Write command item
  class ddr3_mrw_seq_item extends ddr3_cmd_seq_item;
    `uvm_object_utils(ddr3_mrw_seq_item)

    logic [1:0] mr_sel;     // Mode register select (MR0-MR3)
    logic [15:0] mr_data;   // Mode register data

    function new(string name = "ddr3_mrw_seq_item");
      super.new(name);
    endfunction
  endclass

  // ZQ Calibration command item
  class ddr3_zqc_seq_item extends ddr3_cmd_seq_item;
    `uvm_object_utils(ddr3_zqc_seq_item)

    bit long_cal;  // 0 = ZQCS (short), 1 = ZQCL (long)

    function new(string name = "ddr3_zqc_seq_item");
      super.new(name);
    endfunction
  endclass

endpackage : ddr3_cmds_pkg

`endif
