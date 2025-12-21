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

### ⚠️ Partial Support

1. **Queue + Foreach Constraints**: Size constraints work, but element constraints are NOT applied
   - The queue will be sized correctly based on size constraints
   - Element constraints (foreach) run on an empty queue, so no element constraints are applied
   - Elements will be filled with random values after resize
   - Warning: CONSTRAINTIGN warns about this limitation
   - Example:
     ```systemverilog
     rand bit [3:0] wstrb [$:256];
     constraint size_c { wstrb.size() == len; }
     constraint elem_c { foreach(wstrb[i]) wstrb[i] != 0; }  // NOT APPLIED!
     ```
   - Result: Queue is resized to `len`, elements get random values (may include 0)

### ✅ Also Working

1. **$countones in Constraints**: Works correctly
   - Simple `$countones()` constraints work correctly
   - `foreach` with `$countones()` on fixed arrays works
   - Only limited when combined with queue size constraints (see above)

2. **Coverage**: `uvm_subscriber` is implemented. Covergroups are supported via `--coverage-user`.

### 📝 Test Status

**Verilator UVM Unit Tests**: 24 passed, 0 failed, 2 skipped

| Test | Status |
|------|--------|
| t_uvm_run_test | ✅ PASS |
| t_uvm_config_db | ✅ PASS |
| t_uvm_tlm_analysis_fifo | ✅ PASS |
| t_uvm_full_sim | ✅ PASS |
| t_constraint_countones | ✅ PASS |
| t_constraint_countones_fixed | ✅ PASS |
| t_constraint_queue_simple | ✅ PASS |
| t_constraint_queue_foreach | ✅ PASS (size works, element constraints not applied) |

### ⚠️ axi4_avip Testbench Status

The mbits-mirafra axi4_avip testbench now:
1. **Compiles successfully** with `--top-module tb_top`
2. **Runs UVM phases** (build, connect, run) correctly
3. **Fails at randomization** due to `foreach` constraints on queues with dynamic size:
   ```systemverilog
   // These constraints in axi4_master_tx cause the failure:
   constraint wstrb_c3 {foreach(wstrb[i]) wstrb[i]!=0; }
   constraint wstrb_c4 {foreach(wstrb[i]) $countones(wstrb[i]) == 2**awsize;}
   ```

**Workaround**: Move foreach constraints to `post_randomize()`:
```systemverilog
function void post_randomize();
  foreach(wstrb[i]) begin
    // Ensure wstrb is non-zero with correct number of bits
    if (wstrb[i] == 0 || $countones(wstrb[i]) != 2**awsize) begin
      wstrb[i] = (1 << (2**awsize)) - 1;  // Default valid strobe
    end
  end
endfunction
```

**Build command**:
```bash
cd ~/repos/mbits-mirafra/axi4_avip/sim
verilator --binary --timing --top-module tb_top \
  -f axi4_compile_full.f tb_top.sv \
  -Wno-CONSTRAINTIGN -Wno-CASEINCOMPLETE -Wno-WIDTH \
  -Wno-UNOPTFLAT -Wno-CASTCONST
```

### ✅ Recent Fixes

1. **Inline constraints + queue size** (commit a22b7ed3a):
   - Fixed: `randomize() with {...}` now correctly resizes queues
   - Bug was: `__Vresize_constrained_arrays()` not called for inline constraints
   - Test: `t_constraint_inline_queue_size.py`

### 📁 Key Files

- `/Users/ahle/repos/verilator/include/uvm_pkg.sv` - UVM package implementation
- `/Users/ahle/repos/verilator/include/uvm_macros.svh` - UVM macros
- `/Users/ahle/repos/mbits-mirafra/axi4_avip/` - Real-world UVM testbench for testing
