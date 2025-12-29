// DESCRIPTION: Verilator: Test UVM TLM generic payload
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test uvm_tlm_generic_payload class

`include "uvm_macros.svh"

module t;
  import uvm_pkg::*;

  // Test
  class test extends uvm_test;
    `uvm_component_utils(test)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
      uvm_tlm_generic_payload gp;
      uvm_tlm_generic_payload gp2;
      byte unsigned data[];
      byte unsigned be[];

      phase.raise_objection(this);

      `uvm_info("TEST", "Testing uvm_tlm_generic_payload", UVM_LOW)

      // Test creation
      gp = new("gp");

      // Test address
      `uvm_info("TEST", "Testing address", UVM_LOW)
      gp.set_address(64'hDEAD_BEEF_CAFE_1234);
      if (gp.get_address() != 64'hDEAD_BEEF_CAFE_1234) begin
        `uvm_error("TEST", $sformatf("Address mismatch: 0x%0h", gp.get_address()))
      end else begin
        `uvm_info("TEST", "Address test PASSED", UVM_LOW)
      end

      // Test command
      `uvm_info("TEST", "Testing command", UVM_LOW)
      gp.set_command(UVM_TLM_WRITE_COMMAND);
      if (!gp.is_write()) begin
        `uvm_error("TEST", "is_write() should return 1")
      end
      if (gp.is_read()) begin
        `uvm_error("TEST", "is_read() should return 0")
      end
      if (gp.get_command() != UVM_TLM_WRITE_COMMAND) begin
        `uvm_error("TEST", "get_command() mismatch")
      end

      gp.set_read();
      if (!gp.is_read()) begin
        `uvm_error("TEST", "set_read() didn't work")
      end
      gp.set_write();
      if (!gp.is_write()) begin
        `uvm_error("TEST", "set_write() didn't work")
      end
      `uvm_info("TEST", "Command test PASSED", UVM_LOW)

      // Test data
      `uvm_info("TEST", "Testing data", UVM_LOW)
      data = new[4];
      data[0] = 8'hAA;
      data[1] = 8'hBB;
      data[2] = 8'hCC;
      data[3] = 8'hDD;
      gp.set_data(data);
      gp.set_data_length(4);

      if (gp.get_data_length() != 4) begin
        `uvm_error("TEST", $sformatf("Data length mismatch: %0d", gp.get_data_length()))
      end

      begin
        byte unsigned rdata[];
        gp.get_data(rdata);
        if (rdata.size() != 4 || rdata[0] != 8'hAA || rdata[3] != 8'hDD) begin
          `uvm_error("TEST", "Data content mismatch")
        end else begin
          `uvm_info("TEST", "Data test PASSED", UVM_LOW)
        end
      end

      // Test response status
      `uvm_info("TEST", "Testing response status", UVM_LOW)
      if (!gp.is_response_error()) begin
        `uvm_error("TEST", "Initial response should be error (INCOMPLETE)")
      end

      gp.set_response_status(UVM_TLM_OK_RESPONSE);
      if (!gp.is_response_ok()) begin
        `uvm_error("TEST", "is_response_ok() should return 1")
      end
      if (gp.get_response_string() != "OK") begin
        `uvm_error("TEST", $sformatf("Response string wrong: %s", gp.get_response_string()))
      end

      gp.set_response_status(UVM_TLM_ADDRESS_ERROR_RESPONSE);
      if (gp.is_response_ok()) begin
        `uvm_error("TEST", "ADDRESS_ERROR should not be OK")
      end
      if (gp.get_response_string() != "ADDRESS_ERROR") begin
        `uvm_error("TEST", $sformatf("Response string wrong: %s", gp.get_response_string()))
      end
      `uvm_info("TEST", "Response status test PASSED", UVM_LOW)

      // Test byte enable
      `uvm_info("TEST", "Testing byte enable", UVM_LOW)
      be = new[2];
      be[0] = 8'hFF;
      be[1] = 8'h0F;
      gp.set_byte_enable(be);
      gp.set_byte_enable_length(2);

      if (gp.get_byte_enable_length() != 2) begin
        `uvm_error("TEST", $sformatf("Byte enable length mismatch: %0d", gp.get_byte_enable_length()))
      end

      begin
        byte unsigned rbe[];
        gp.get_byte_enable(rbe);
        if (rbe.size() != 2 || rbe[0] != 8'hFF || rbe[1] != 8'h0F) begin
          `uvm_error("TEST", "Byte enable content mismatch")
        end else begin
          `uvm_info("TEST", "Byte enable test PASSED", UVM_LOW)
        end
      end

      // Test streaming width
      `uvm_info("TEST", "Testing streaming width", UVM_LOW)
      gp.set_streaming_width(64);
      if (gp.get_streaming_width() != 64) begin
        `uvm_error("TEST", $sformatf("Streaming width mismatch: %0d", gp.get_streaming_width()))
      end else begin
        `uvm_info("TEST", "Streaming width test PASSED", UVM_LOW)
      end

      // Test DMI
      `uvm_info("TEST", "Testing DMI", UVM_LOW)
      gp.set_dmi_allowed(1);
      if (!gp.is_dmi_allowed()) begin
        `uvm_error("TEST", "DMI should be allowed")
      end
      gp.set_dmi_allowed(0);
      if (gp.is_dmi_allowed()) begin
        `uvm_error("TEST", "DMI should not be allowed")
      end
      `uvm_info("TEST", "DMI test PASSED", UVM_LOW)

      // Test convert2string
      `uvm_info("TEST", "Testing convert2string", UVM_LOW)
      gp.set_response_status(UVM_TLM_OK_RESPONSE);
      `uvm_info("TEST", $sformatf("GP: %s", gp.convert2string()), UVM_LOW)

      // Test copy
      `uvm_info("TEST", "Testing copy", UVM_LOW)
      gp2 = new("gp2");
      gp2.copy(gp);
      if (gp2.get_address() != gp.get_address()) begin
        `uvm_error("TEST", "Copy: address mismatch")
      end
      if (gp2.get_command() != gp.get_command()) begin
        `uvm_error("TEST", "Copy: command mismatch")
      end
      if (gp2.get_data_length() != gp.get_data_length()) begin
        `uvm_error("TEST", "Copy: data length mismatch")
      end
      `uvm_info("TEST", "Copy test PASSED", UVM_LOW)

      // Test compare
      `uvm_info("TEST", "Testing compare", UVM_LOW)
      if (!gp.compare(gp2)) begin
        `uvm_error("TEST", "Compare: gp and gp2 should match")
      end
      gp2.set_address(64'h1234);
      if (gp.compare(gp2)) begin
        `uvm_error("TEST", "Compare: gp and gp2 should differ after address change")
      end
      `uvm_info("TEST", "Compare test PASSED", UVM_LOW)

      // Test TLM enums (values, not .name() which is unsupported)
      `uvm_info("TEST", "Testing TLM enums", UVM_LOW)
      if (UVM_TLM_READ_COMMAND != 0) begin
        `uvm_error("TEST", "UVM_TLM_READ_COMMAND should be 0")
      end
      if (UVM_TLM_WRITE_COMMAND != 1) begin
        `uvm_error("TEST", "UVM_TLM_WRITE_COMMAND should be 1")
      end
      if (UVM_TLM_BEGIN_REQ != 1) begin
        `uvm_error("TEST", "UVM_TLM_BEGIN_REQ should be 1")
      end
      if (UVM_TLM_OK_RESPONSE != 1) begin
        `uvm_error("TEST", "UVM_TLM_OK_RESPONSE should be 1")
      end
      `uvm_info("TEST", "TLM enum test PASSED", UVM_LOW)

      `uvm_info("TEST", "All uvm_tlm_generic_payload tests PASSED", UVM_LOW)

      phase.drop_objection(this);
    endtask

    virtual function void report_phase(uvm_phase phase);
      super.report_phase(phase);
      $write("*-* All Finished *-*\n");
    endfunction
  endclass

  initial begin
    run_test("test");
  end
endmodule
