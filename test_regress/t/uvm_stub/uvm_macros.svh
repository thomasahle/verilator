// Minimal UVM macros stub for testing assertions
`define uvm_info(ID, MSG, VERB)
`define uvm_error(ID, MSG)
`define uvm_warning(ID, MSG)
`define uvm_fatal(ID, MSG) $fatal(1, MSG)
