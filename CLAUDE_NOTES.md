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

1. **Queue + Foreach Constraints**: Size constraints combined with foreach element constraints on queues don't work
   - Root cause: Element constraints are generated BEFORE queue size is solved
   - Warning: CONSTRAINTIGN warns about this combination
   - Workaround: Use fixed-size arrays or separate randomization calls
   - Example that fails:
     ```systemverilog
     rand bit [3:0] wstrb [$:256];
     constraint size_c { wstrb.size() == len; }
     constraint elem_c { foreach(wstrb[i]) wstrb[i] != 0; }  // Fails!
     ```
   - Example that works:
     ```systemverilog
     rand bit [3:0] wstrb [4];  // Fixed size array
     constraint elem_c { foreach(wstrb[i]) wstrb[i] != 0; }  // Works!
     ```

2. **$countones in Constraints**: ✅ NOW WORKING
   - Simple `$countones()` constraints work correctly
   - `foreach` with `$countones()` on fixed arrays works
   - Only fails when combined with queue size constraints (see #1)

3. **Coverage**: `uvm_subscriber` is implemented. Covergroups are supported via `--coverage-user`.

### 📝 Test Status

**Verilator UVM Unit Tests**: 24 passed, 0 failed, 2 skipped

| Test | Status |
|------|--------|
| axi4_base_test | ✅ PASS (completes all phases) |
| axi4_blocking_write_read_test | ❌ FAIL (queue+foreach constraint) |
| axi4_read_test | ⚠️ RUNS (may hang in driver handshake) |
| t_uvm_run_test | ✅ PASS |
| t_uvm_config_db | ✅ PASS |
| t_uvm_tlm_analysis_fifo | ✅ PASS |
| t_uvm_full_sim | ✅ PASS |
| t_constraint_countones | ✅ PASS |
| t_constraint_countones_fixed | ✅ PASS |

### 📁 Key Files

- `/Users/ahle/repos/verilator/include/uvm_pkg.sv` - UVM package implementation
- `/Users/ahle/repos/verilator/include/uvm_macros.svh` - UVM macros
- `/Users/ahle/repos/mbits-mirafra/axi4_avip/` - Real-world UVM testbench for testing
