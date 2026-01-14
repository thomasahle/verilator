// DESCRIPTION: Verilator: Test struct-to-class converter pattern for BFM communication
// This pattern is used in AVIPs to convert UVM sequence items to plain structs
// for passing data between HVL (UVM testbench) and HDL (BFM interfaces)
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define UVM_NO_DPI
`define UVM_REGEX_NO_DPI

// Transfer type enum
typedef enum bit [1:0] {
   READ  = 2'b00,
   WRITE = 2'b01,
   IDLE  = 2'b10
} transfer_type_e;

// Plain struct for BFM communication (HDL side)
typedef struct packed {
   bit [7:0]  addr;
   bit [31:0] data;
   bit [1:0]  transfer_type;
   bit        error;
} transfer_char_s;

// Simple BFM interface that uses structs
interface bfm_if(input logic clk);
   logic [7:0]  addr;
   logic [31:0] data;
   logic [1:0]  transfer_type;
   logic        error;
   logic        valid;

   // BFM task: Drive transaction from struct
   task drive(input transfer_char_s s);
      @(posedge clk);
      addr <= s.addr;
      data <= s.data;
      transfer_type <= s.transfer_type;
      error <= s.error;
      valid <= 1;
      @(posedge clk);
      valid <= 0;
   endtask

   // BFM task: Sample transaction to struct
   task sample(output transfer_char_s s);
      // Wait for valid to go high
      while (!valid) @(posedge clk);
      // Sample the data
      s.addr = addr;
      s.data = data;
      s.transfer_type = transfer_type;
      s.error = error;
      // Wait for valid to go low (transaction complete)
      while (valid) @(posedge clk);
   endtask
endinterface

module t;
   import uvm_pkg::*;
   `include "uvm_macros.svh"

   // UVM sequence item class (HVL side)
   class my_tx extends uvm_sequence_item;
      `uvm_object_utils(my_tx)

      bit [7:0]  addr;
      bit [31:0] data;
      transfer_type_e transfer_type;
      bit error;

      function new(string name = "my_tx");
         super.new(name);
      endfunction

      virtual function string convert2string();
         return $sformatf("addr=%h data=%h type=%s err=%b",
                          addr, data, transfer_type.name(), error);
      endfunction
   endclass

   // Converter class - static methods for struct/class conversion
   class tx_converter;

      // Convert class to struct (for driver -> BFM)
      static function void from_class(input my_tx tx, output transfer_char_s s);
         s.addr = tx.addr;
         s.data = tx.data;
         s.transfer_type = tx.transfer_type;
         s.error = tx.error;
      endfunction

      // Convert struct to class (for BFM -> monitor)
      static function void to_class(input transfer_char_s s, output my_tx tx);
         tx = new("converted_tx");
         tx.addr = s.addr;
         tx.data = s.data;
         if (!$cast(tx.transfer_type, s.transfer_type)) begin
            tx.transfer_type = IDLE;
         end
         tx.error = s.error;
      endfunction

   endclass

   // Driver proxy that uses converter
   class driver_proxy extends uvm_component;
      `uvm_component_utils(driver_proxy)

      virtual bfm_if vif;
      int items_driven;

      function new(string name = "", uvm_component parent = null);
         super.new(name, parent);
         items_driven = 0;
      endfunction

      task drive_item(my_tx tx);
         transfer_char_s struct_packet;
         // Convert class to struct
         tx_converter::from_class(tx, struct_packet);
         `uvm_info(get_type_name(), $sformatf("Driving: %s", tx.convert2string()), UVM_LOW)
         // Drive to BFM
         vif.drive(struct_packet);
         items_driven++;
      endtask
   endclass

   // Monitor proxy that uses converter
   class monitor_proxy extends uvm_component;
      `uvm_component_utils(monitor_proxy)

      virtual bfm_if vif;
      uvm_analysis_port #(my_tx) ap;
      int items_sampled;

      function new(string name = "", uvm_component parent = null);
         super.new(name, parent);
         items_sampled = 0;
      endfunction

      function void build_phase(uvm_phase phase);
         super.build_phase(phase);
         ap = new("ap", this);
      endfunction

      task sample_item();
         transfer_char_s struct_packet;
         my_tx tx;
         // Sample from BFM
         vif.sample(struct_packet);
         // Convert struct to class
         tx_converter::to_class(struct_packet, tx);
         `uvm_info(get_type_name(), $sformatf("Sampled: %s", tx.convert2string()), UVM_LOW)
         ap.write(tx);
         items_sampled++;
      endtask
   endclass

   // Subscriber to receive monitored transactions (renamed from checker)
   class tx_checker extends uvm_subscriber #(my_tx);
      `uvm_component_utils(tx_checker)

      my_tx received[$];

      function new(string name = "", uvm_component parent = null);
         super.new(name, parent);
      endfunction

      virtual function void write(my_tx t);
         `uvm_info(get_type_name(), $sformatf("Received: %s", t.convert2string()), UVM_LOW)
         received.push_back(t);
      endfunction
   endclass

   // Test module
   logic clk = 0;
   always #5 clk = ~clk;

   bfm_if bfm(.clk(clk));

   initial begin
      driver_proxy drv;
      monitor_proxy mon;
      tx_checker chk;
      uvm_phase phase;
      my_tx tx;

      `uvm_info("TOP", "Starting struct converter test", UVM_LOW)

      // Create components
      drv = new("drv", null);
      mon = new("mon", null);
      chk = new("chk", null);

      // Assign virtual interfaces
      drv.vif = bfm;
      mon.vif = bfm;

      // Build
      phase = new("build");
      mon.build_phase(phase);
      chk.build_phase(phase);

      // Connect
      mon.ap.connect(chk.analysis_export);

      // Drive some transactions
      fork
         begin
            // Driver side - use direct assignment instead of constraints
            for (int i = 0; i < 3; i++) begin
               tx = new($sformatf("tx_%0d", i));
               tx.addr = i * 16;
               tx.data = i * 100;
               tx.transfer_type = (i % 2 == 0) ? WRITE : READ;
               tx.error = 0;
               drv.drive_item(tx);
            end
         end
         begin
            // Monitor side
            for (int i = 0; i < 3; i++) begin
               mon.sample_item();
            end
         end
      join

      #10;

      // Check results
      `uvm_info("TOP", $sformatf("Driver drove %0d items", drv.items_driven), UVM_LOW)
      `uvm_info("TOP", $sformatf("Monitor sampled %0d items", mon.items_sampled), UVM_LOW)
      `uvm_info("TOP", $sformatf("Checker received %0d items", chk.received.size()), UVM_LOW)

      if (drv.items_driven == 3 && mon.items_sampled == 3 && chk.received.size() == 3) begin
         // Verify data integrity
         if (chk.received[0].addr == 0 && chk.received[1].addr == 16 && chk.received[2].addr == 32) begin
            $display("*-* All Finished *-*");
         end else begin
            $display("FAIL: Address mismatch");
            $stop;
         end
      end else begin
         $display("FAIL: Count mismatch");
         $stop;
      end
      $finish;
   end

endmodule
