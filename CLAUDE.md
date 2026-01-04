# Claude Code Instructions for Verilator

## Running Simulations

**CRITICAL: Kill simulation processes properly**

When running simulations (especially with VCD waveform output), be aware that:
1. `timeout` command may only kill the parent shell/pipe, not the underlying simulator process
2. vvp (Icarus Verilog) and other simulators can continue running in the background
3. Waveform dumps (.vcd files) can grow to 100s of GB if simulations run unchecked

**Before running tests with waveforms:**
- Check for existing simulator processes: `ps aux | grep -E "vvp|verilator|VTb" | grep -v grep`
- Kill any orphaned simulators before starting new tests

**When a test times out or fails:**
- Kill process groups, not just the shell: use `pkill -9 vvp` or similar
- Check for large .vcd files and remove them: `find . -name "*.vcd" -size +100M`
- Monitor disk space: `df -h .`

**Disk space management:**
- Clean up test artifacts regularly: `rm -rf test_regress/obj_vlt* test_regress/obj_vltmt*`
- The test_regress/ directory can grow to 10GB+ with build artifacts
- Always clean up large waveform files after test runs
