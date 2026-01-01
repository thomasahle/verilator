// DESCRIPTION: Verilator: Verilog Test module
//
// Test $cast with clone() pattern - common in UVM
// Pattern: $cast(clone_obj, original.clone())
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Anthropic.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

// Base transaction class (like uvm_sequence_item)
class BaseTransaction;
    int id;
    string name;

    function new(string name = "base_tx");
        this.name = name;
        this.id = 0;
    endfunction

    virtual function BaseTransaction clone();
        BaseTransaction tx = new(this.name);
        tx.id = this.id;
        return tx;
    endfunction

    virtual function void copy(BaseTransaction rhs);
        this.id = rhs.id;
        this.name = rhs.name;
    endfunction

    virtual function bit compare(BaseTransaction rhs);
        return (this.id == rhs.id) && (this.name == rhs.name);
    endfunction
endclass

// Derived transaction class (like specific protocol transaction)
class DerivedTransaction extends BaseTransaction;
    int addr;
    int data;
    bit [3:0] strb;

    function new(string name = "derived_tx");
        super.new(name);
        this.addr = 0;
        this.data = 0;
        this.strb = 4'hF;
    endfunction

    virtual function BaseTransaction clone();
        DerivedTransaction tx = new(this.name);
        tx.id = this.id;
        tx.addr = this.addr;
        tx.data = this.data;
        tx.strb = this.strb;
        return tx;
    endfunction

    virtual function void copy(BaseTransaction rhs);
        DerivedTransaction rhs_d;
        super.copy(rhs);
        if ($cast(rhs_d, rhs)) begin
            this.addr = rhs_d.addr;
            this.data = rhs_d.data;
            this.strb = rhs_d.strb;
        end
    endfunction

    virtual function bit compare(BaseTransaction rhs);
        DerivedTransaction rhs_d;
        if (!super.compare(rhs)) return 0;
        if (!$cast(rhs_d, rhs)) return 0;
        return (this.addr == rhs_d.addr) &&
               (this.data == rhs_d.data) &&
               (this.strb == rhs_d.strb);
    endfunction
endclass

// Further derived class
class ExtendedTransaction extends DerivedTransaction;
    int burst_len;
    int burst_type;

    function new(string name = "extended_tx");
        super.new(name);
        this.burst_len = 1;
        this.burst_type = 0;
    endfunction

    virtual function BaseTransaction clone();
        ExtendedTransaction tx = new(this.name);
        tx.id = this.id;
        tx.addr = this.addr;
        tx.data = this.data;
        tx.strb = this.strb;
        tx.burst_len = this.burst_len;
        tx.burst_type = this.burst_type;
        return tx;
    endfunction

    virtual function bit compare(BaseTransaction rhs);
        ExtendedTransaction rhs_e;
        if (!super.compare(rhs)) return 0;
        if (!$cast(rhs_e, rhs)) return 0;
        return (this.burst_len == rhs_e.burst_len) &&
               (this.burst_type == rhs_e.burst_type);
    endfunction
endclass

module t_castdyn_clone;
    BaseTransaction base_tx;
    DerivedTransaction derived_tx, derived_clone;
    ExtendedTransaction extended_tx, extended_clone;
    int cast_result;

    initial begin
        $display("Test: $cast with clone() pattern (UVM pattern)");

        // Test 1: Clone DerivedTransaction and cast back
        $display("\n=== Test 1: Clone derived, cast to derived ===");
        derived_tx = new("test_derived");
        derived_tx.id = 42;
        derived_tx.addr = 32'hDEAD_BEEF;
        derived_tx.data = 32'h1234_5678;
        derived_tx.strb = 4'hA;

        // Common UVM pattern: $cast(clone, original.clone())
        cast_result = $cast(derived_clone, derived_tx.clone());
        `checkh(cast_result, 1)
        `checkh(derived_clone.id, 42)
        `checkh(derived_clone.addr, 32'hDEAD_BEEF)
        `checkh(derived_clone.data, 32'h1234_5678)
        `checkh(derived_clone.strb, 4'hA)
        `checkh(derived_tx.compare(derived_clone), 1)
        $display("  Clone successful, compare passed");

        // Test 2: Clone ExtendedTransaction
        $display("\n=== Test 2: Clone extended, cast to extended ===");
        extended_tx = new("test_extended");
        extended_tx.id = 99;
        extended_tx.addr = 32'hCAFE_BABE;
        extended_tx.data = 32'hABCD_EF01;
        extended_tx.burst_len = 8;
        extended_tx.burst_type = 1;

        cast_result = $cast(extended_clone, extended_tx.clone());
        `checkh(cast_result, 1)
        `checkh(extended_clone.id, 99)
        `checkh(extended_clone.burst_len, 8)
        `checkh(extended_clone.burst_type, 1)
        `checkh(extended_tx.compare(extended_clone), 1)
        $display("  Clone successful, compare passed");

        // Test 3: Clone to base reference then cast down
        $display("\n=== Test 3: Clone to base, cast down ===");
        base_tx = extended_tx.clone();  // Returns BaseTransaction handle
        cast_result = $cast(extended_clone, base_tx);
        `checkh(cast_result, 1)
        `checkh(extended_clone.burst_len, 8)
        $display("  Downcast successful");

        // Test 4: Failed cast (derived to extended)
        $display("\n=== Test 4: Failed cast (derived to extended) ===");
        derived_tx = new("plain_derived");
        cast_result = $cast(extended_clone, derived_tx);
        `checkh(cast_result, 0)
        $display("  Cast correctly failed (derived is not extended)");

        // Test 5: Cast after clone in comparison
        $display("\n=== Test 5: Cast in comparison function ===");
        extended_tx.id = 100;
        extended_clone.id = 100;
        `checkh(extended_tx.compare(extended_clone), 1)
        extended_clone.burst_len = 16;  // Make different
        `checkh(extended_tx.compare(extended_clone), 0)
        $display("  Comparison with internal cast works");

        // Test 6: Copy using cast
        $display("\n=== Test 6: Copy using cast ===");
        derived_tx = new("copy_test");
        derived_tx.addr = 32'h1111_1111;
        derived_clone = new("target");
        derived_clone.copy(derived_tx);
        `checkh(derived_clone.addr, 32'h1111_1111)
        $display("  Copy with cast successful");

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
