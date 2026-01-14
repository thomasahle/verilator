// DESCRIPTION: Verilator: Verilog Test module
//
// Test virtual interface with config_db - pattern from AVIPs
// Tests storing and retrieving virtual interfaces via config_db
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Anthropic.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

// Simple AXI-like interface
interface axi_if (input logic clk);
    logic [31:0] awaddr;
    logic [31:0] wdata;
    logic [31:0] araddr;
    logic [31:0] rdata;
    logic awvalid, awready;
    logic wvalid, wready;
    logic arvalid, arready;
    logic rvalid, rready;
endinterface

// Simple config_db for virtual interfaces
class config_db_vif;
    static virtual axi_if vif_db[string];

    static function void set(string scope, string name, virtual axi_if value);
        string key = {scope, ".", name};
        vif_db[key] = value;
        $display("[config_db] SET %s", key);
    endfunction

    static function bit get(string scope, string name, output virtual axi_if value);
        string key = {scope, ".", name};
        if (vif_db.exists(key)) begin
            value = vif_db[key];
            $display("[config_db] GET %s found", key);
            return 1;
        end
        key = {"*.", name};
        if (vif_db.exists(key)) begin
            value = vif_db[key];
            $display("[config_db] GET %s found via wildcard", key);
            return 1;
        end
        $display("[config_db] GET %s not found", key);
        return 0;
    endfunction
endclass

// Driver class (like UVM driver)
class axi_driver;
    virtual axi_if vif;
    string name;

    function new(string name);
        this.name = name;
    endfunction

    function bit get_vif();
        return config_db_vif::get("*", "axi_vif", vif);
    endfunction

    task drive_write(input logic [31:0] addr, input logic [31:0] data);
        $display("[%0t] %s: Driving write addr=0x%h data=0x%h", $time, name, addr, data);
        @(posedge vif.clk);
        vif.awaddr = addr;
        vif.awvalid = 1;
        vif.wdata = data;
        vif.wvalid = 1;
        @(posedge vif.clk);
        vif.awvalid = 0;
        vif.wvalid = 0;
    endtask

    task drive_read(input logic [31:0] addr, output logic [31:0] data);
        $display("[%0t] %s: Driving read addr=0x%h", $time, name, addr);
        @(posedge vif.clk);
        vif.araddr = addr;
        vif.arvalid = 1;
        @(posedge vif.clk);
        vif.arvalid = 0;
        @(posedge vif.clk);
        data = vif.rdata;
        $display("[%0t] %s: Read data=0x%h", $time, name, data);
    endtask
endclass

// Monitor class
class axi_monitor;
    virtual axi_if vif;
    string name;
    int write_count = 0;
    int read_count = 0;

    function new(string name);
        this.name = name;
    endfunction

    function bit get_vif();
        return config_db_vif::get("*", "axi_vif", vif);
    endfunction

    // Non-blocking check for transactions
    function void check_transactions();
        if (vif.awvalid && vif.awready) begin
            write_count++;
            $display("[%0t] %s: Observed write #%0d addr=0x%h", $time, name, write_count, vif.awaddr);
        end
        if (vif.arvalid && vif.arready) begin
            read_count++;
            $display("[%0t] %s: Observed read #%0d addr=0x%h", $time, name, read_count, vif.araddr);
        end
    endfunction
endclass

// Agent class
class axi_agent;
    axi_driver driver;
    axi_monitor monitor;
    string name;

    function new(string name);
        this.name = name;
    endfunction

    function void build();
        driver = new({name, ".driver"});
        monitor = new({name, ".monitor"});

        if (!driver.get_vif()) begin
            $display("[%s] ERROR: Could not get vif for driver", name);
        end
        if (!monitor.get_vif()) begin
            $display("[%s] ERROR: Could not get vif for monitor", name);
        end
    endfunction
endclass

module t_uvm_config_db_vif;
    logic clk = 0;
    always #5 clk = ~clk;

    // Instantiate interface
    axi_if axi_bus(clk);

    // Simple slave response
    always @(posedge clk) begin
        axi_bus.awready <= axi_bus.awvalid;
        axi_bus.wready <= axi_bus.wvalid;
        axi_bus.arready <= axi_bus.arvalid;
        if (axi_bus.arvalid) begin
            axi_bus.rdata <= axi_bus.araddr + 32'h100;
            axi_bus.rvalid <= 1;
        end else begin
            axi_bus.rvalid <= 0;
        end
    end

    axi_agent agent;
    logic [31:0] read_data;

    initial begin
        $display("Test: Virtual interface config_db pattern (AVIP pattern)");

        // Store virtual interface in config_db
        config_db_vif::set("*", "axi_vif", axi_bus);

        // Create and build agent
        agent = new("axi_agent");
        agent.build();

        // Verify vif was retrieved
        `checkh(agent.driver.vif != null, 1)
        `checkh(agent.monitor.vif != null, 1)

        // Wait for clock to stabilize
        repeat(2) @(posedge clk);

        // Drive some transactions and check monitor
        $display("\n=== Driving transactions ===");
        agent.driver.drive_write(32'h1000, 32'hDEAD_BEEF);
        agent.monitor.check_transactions();

        agent.driver.drive_write(32'h2000, 32'hCAFE_BABE);
        agent.monitor.check_transactions();

        agent.driver.drive_read(32'h3000, read_data);
        agent.monitor.check_transactions();
        `checkh(read_data, 32'h3100)

        $display("\nMonitor counts: writes=%0d, reads=%0d", agent.monitor.write_count, agent.monitor.read_count);

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
