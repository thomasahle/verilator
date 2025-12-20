# Claude Session Notes

## IMPORTANT: Long Output Handling

When running commands that produce long output (compilation, test runs, g++, etc.):
- **ALWAYS pipe output to a file** to avoid overloading context window
- Example: `verilator ... 2>&1 > /tmp/compile.log && tail -50 /tmp/compile.log`
- Example: `make 2>&1 | tee /tmp/build.log && tail -100 /tmp/build.log`
- Then read specific parts of the log file as needed

## Current Goal

Full UVM support for Verilator - NO WORKAROUNDS. The goal is to fix Verilator itself to support:
- Inherited type parameters in parameterized classes
- All standard UVM patterns without requiring code modifications

## UVM Support Status

### ✅ Working Features

1. **Core UVM Classes**: uvm_object, uvm_component, uvm_test, uvm_env, uvm_agent, uvm_driver, uvm_monitor, uvm_scoreboard
2. **Factory**: `uvm_component_utils`, `uvm_object_utils` macros with auto-registration
3. **Phasing**: All standard phases (build, connect, run, report, etc.) with proper hierarchy traversal
4. **Config DB**: `uvm_config_db::set()` and `get()` with wildcard pattern matching
5. **Objections**: Phase objections for run_phase completion
6. **Sequences**: `uvm_sequence`, `uvm_sequencer`, `uvm_do*` macros, `uvm_declare_p_sequencer`
7. **TLM Ports**: `uvm_analysis_port`, `uvm_analysis_imp`, `uvm_tlm_fifo`, `uvm_tlm_analysis_fifo`
8. **Run Test**: `run_test()` with `+UVM_TESTNAME` command line support
9. **Hierarchy**: Parent/child relationships, `get_full_name()`, component lookup

### ❌ Known Limitations

1. **Constraint Solver**: `$countones()` and some complex constraint expressions not supported
   - Tests with complex AXI4 constraints fail (e.g., `axi4_blocking_write_read_test`)
   - Simple tests work (e.g., `axi4_base_test`)

2. **Coverage**: `uvm_subscriber` and functional coverage not fully implemented

### 📝 Test Status

| Test | Status |
|------|--------|
| axi4_base_test | ✅ PASS |
| axi4_blocking_write_read_test | ❌ FAIL (constraint solver) |
| t_uvm_sequence_basic | ✅ PASS |
| t_uvm_tlm_analysis_fifo | ✅ PASS |
| t_uvm_factory | ✅ PASS |

### 📁 Key Files

- `/Users/ahle/repos/verilator/include/uvm_pkg.sv` - UVM package implementation
- `/Users/ahle/repos/verilator/include/uvm_macros.svh` - UVM macros
- `/Users/ahle/repos/mbits-mirafra/axi4_avip/` - Real-world UVM testbench for testing
