// DESCRIPTION: Verilator: Test covergroup sample parameter with same name as type
// This code is in the Public Domain.
//
// Test that covergroup sample function parameters can have the same name
// as their type (e.g., "Config Config" instead of "Config cfg").
// This is valid SystemVerilog and should be supported.

class Config;
  int value;
endclass

class Transaction;
  int data;
  logic [7:0] addr;
endclass

class Coverage;
  int sample_count = 0;

  // Test case 1: Parameter with same name as type (lowercase)
  covergroup cg1 with function sample (Config Config);
    option.per_instance = 1;
    VALUE_CP: coverpoint Config.value {
      bins low = {[0:9]};
      bins high = {[10:$]};
    }
  endgroup

  // Test case 2: Parameter with same name as type (CamelCase)
  covergroup cg2 with function sample (Transaction Transaction, int count);
    option.per_instance = 1;
    DATA_CP: coverpoint Transaction.data;
    ADDR_CP: coverpoint Transaction.addr;
    COUNT_CP: coverpoint count;
  endgroup

  // Test case 3: Multiple parameters, some same name, some different
  covergroup cg3 with function sample (Config Config, Transaction tx, int val);
    option.per_instance = 1;
    CFG_VAL: coverpoint Config.value;
    TX_DATA: coverpoint tx.data;
    VAL_CP: coverpoint val;
  endgroup

  function new();
    cg1 = new();
    cg2 = new();
    cg3 = new();
  endfunction

  function void do_sample();
    Config cfg = new;
    Transaction tx = new;

    cfg.value = 5;
    tx.data = 100;
    tx.addr = 8'hAB;

    cg1.sample(cfg);
    cg2.sample(tx, 42);
    cg3.sample(cfg, tx, 99);
    sample_count++;
  endfunction
endclass

module t;
  Coverage cov;

  initial begin
    cov = new();
    cov.do_sample();
    cov.do_sample();
    cov.do_sample();

    if (cov.sample_count != 3) begin
      $write("%%Error: Expected 3 samples, got %d\n", cov.sample_count);
      $stop;
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
