# Verilator → Xcelium Feature Parity Roadmap

## Current State Summary

| Category | Verilator | Xcelium | Gap |
|----------|-----------|---------|-----|
| Language Support | SV/Verilog | SV/Verilog/VHDL/AMS | VHDL, AMS missing |
| Coverage | Line/Toggle/Expr | Full suite + FSM | FSM, Assertion Cov |
| Assertions | Basic SVA | Full SVA/PSL | Multi-cycle, sequences |
| Debug | VCD/FST traces | SimVision GUI | Interactive debug |
| Performance | Single-thread | Multi-core | Parallel sim |
| Low Power | None | Full UPF | UPF support |
| Gate-Level | Basic | Full SDF | Timing annotation |
| Mixed-Signal | None | Full AMS | Analog support |

---

## Phase 1: Coverage Parity (High Priority)

### 1.1 FSM Coverage
**Status**: Not implemented
**Effort**: Medium
**Files**: `V3Coverage.cpp`, new `V3CoverageFsm.cpp`

```
Features needed:
- State detection in always blocks
- State coverage (which states visited)
- Transition coverage (state→state arcs)
- Arc coverage reporting
```

### 1.2 Assertion Coverage
**Status**: Partial (cover statements work, no metrics)
**Effort**: Medium
**Files**: `V3Assert.cpp`, `verilated_cov.cpp`

```
Features needed:
- Per-assertion hit counters
- Pass/fail statistics per assertion
- Assertion coverage percentage
- Integration with coverage reports
```

### 1.3 Branch Coverage Enhancement
**Status**: Basic (implicit in line coverage)
**Effort**: Low
**Files**: `V3Coverage.cpp`

```
Features needed:
- Explicit branch point tracking
- True/false branch counts
- Decision coverage metrics
```

### 1.4 Coverage Merging Tool Enhancement
**Status**: Basic merge exists
**Effort**: Low
**Files**: `verilator_coverage`

```
Features needed:
- Better merge algorithms
- Exclusion file support
- IMC-compatible output format
```

---

## Phase 2: Full SVA Support (High Priority)

### 2.1 Multi-Cycle Assertions
**Status**: Not implemented (degrades to single-cycle)
**Effort**: High
**Files**: `V3Assert.cpp`, `V3AssertPre.cpp`, `V3AssertProp.cpp`

```
Features needed:
- ## (cycle delay) operator
- ##[n:m] (range delay)
- Cycle counter state machines
- Property evaluation across clocks
```

### 2.2 Sequence Operators
**Status**: Simplified/stub implementations
**Effort**: High
**Files**: `V3AssertProp.cpp`

```
Features needed:
- throughout (proper implementation)
- within (proper implementation)
- intersect (proper implementation)
- [*n], [*n:m] repetition
- [=n], [->n] goto repetition
```

### 2.3 $assertcontrol Support
**Status**: Mostly ignored
**Effort**: Medium
**Files**: `V3Assert.cpp`

```
Features needed:
- Runtime assertion enable/disable
- LOCK/UNLOCK support
- PASS_ON/OFF, FAIL_ON/OFF
- Per-assertion control
```

### 2.4 Multi-Clock Properties
**Status**: Not supported
**Effort**: High
**Files**: `V3AssertPre.cpp`

```
Features needed:
- Properties spanning clock domains
- Clock domain crossing in sequences
- Multiple clock event handling
```

---

## Phase 3: Performance (Medium Priority)

### 3.1 Multi-Core Simulation
**Status**: Compile-time threading only
**Effort**: Very High
**Files**: Core architecture change

```
Features needed:
- Runtime parallelization
- Dependency analysis
- Thread-safe event scheduling
- Lock-free data structures
```

### 3.2 Save/Restart (Checkpointing)
**Status**: Basic --savable exists
**Effort**: High
**Files**: `V3Savable.cpp`, runtime

```
Features needed:
- Full state serialization
- C++ application state save
- Restore with new seeds
- Incremental checkpoints
```

### 3.3 Compiled SDF
**Status**: Not implemented
**Effort**: Medium
**Files**: New `V3Sdf.cpp`

```
Features needed:
- SDF file parsing
- Delay annotation
- Timing check insertion
- $sdf_annotate support
```

---

## Phase 4: Debug Features (Medium Priority)

### 4.1 Interactive Debug Mode
**Status**: Not available
**Effort**: Very High
**Files**: New debug infrastructure

```
Features needed:
- Breakpoint support
- Step execution
- Signal watch/modify
- Interactive CLI or GUI
```

### 4.2 Driver Tracing
**Status**: Not implemented
**Effort**: Medium
**Files**: Trace infrastructure

```
Features needed:
- Identify signal drivers
- Trace signal sources
- Conflict detection
```

### 4.3 Transaction-Level Waveforms
**Status**: Not implemented
**Effort**: Medium
**Files**: Trace infrastructure

```
Features needed:
- UVM transaction recording
- High-level waveform abstraction
- Transaction search/filter
```

---

## Phase 5: Low Power (Lower Priority)

### 5.1 UPF Support (IEEE 1801)
**Status**: Not implemented
**Effort**: Very High
**Files**: New `V3Upf.cpp`, power infrastructure

```
Features needed:
- Power domain parsing
- Supply network modeling
- Isolation/retention cells
- Power state simulation
```

### 5.2 X-Propagation Improvements
**Status**: Basic X handling
**Effort**: Medium
**Files**: `V3Unknown.cpp`

```
Features needed:
- X-pessimism removal options
- Accurate X propagation modes
- Low-power X differentiation
```

---

## Phase 6: Advanced Features (Future)

### 6.1 VHDL Support
**Status**: Not supported
**Effort**: Very High (major undertaking)

### 6.2 Mixed-Signal (AMS)
**Status**: Not supported
**Effort**: Very High

### 6.3 Fault Simulation
**Status**: Not supported
**Effort**: High

### 6.4 Machine Learning Optimization
**Status**: Not supported
**Effort**: High

---

## Recommended Implementation Order

### Immediate (This Sprint)
1. **Assertion Coverage Counters** - Add per-assertion hit tracking
2. **FSM State Detection** - Identify FSMs in RTL
3. **Branch Coverage** - Explicit branch tracking

### Short Term (1-2 months)
4. **FSM Coverage Full** - State and transition coverage
5. **Assertion Statistics** - End-of-sim assertion report
6. **## Cycle Delay** - Basic multi-cycle assertions

### Medium Term (3-6 months)
7. **Full Sequence Operators** - throughout, within, intersect
8. **$assertcontrol** - Runtime assertion control
9. **Coverage Tool Enhancements** - Better reporting

### Long Term (6+ months)
10. **Multi-Core Simulation** - Parallel execution
11. **Save/Restart** - Full checkpointing
12. **SDF Timing** - Gate-level timing
13. **Interactive Debug** - Breakpoints, stepping
14. **UPF Low Power** - Power domain simulation

---

## Quick Wins (Can Implement Today)

1. **Assertion hit counters** - Simple counter increment in generated code
2. **FSM detection heuristic** - Pattern match `case(state)` in always blocks
3. **Branch coverage separation** - Track if/else separately from line coverage
4. **Coverage report format** - Add Xcelium-compatible text output

---

## Files to Create/Modify

### New Files Needed
- `src/V3CoverageFsm.cpp` - FSM coverage detection and instrumentation
- `src/V3Sdf.cpp` - SDF parsing and annotation
- `src/V3Upf.cpp` - UPF power domain support
- `src/V3Debug.cpp` - Interactive debug infrastructure

### Major Modifications
- `src/V3Assert.cpp` - Multi-cycle, $assertcontrol, counters
- `src/V3AssertProp.cpp` - Proper sequence operators
- `src/V3Coverage.cpp` - FSM, branch, assertion coverage
- `include/verilated_cov.cpp` - Runtime assertion tracking
- `bin/verilator_coverage` - Enhanced reporting

---

## UVM/SystemVerilog Support Status

### Recently Implemented/Tested Features (January 2025)

| Feature | Status | Notes |
|---------|--------|-------|
| randomize(variable_list) same-class | **Fixed** | Bug fix: only listed vars randomized |
| pre/post_randomize callbacks with inheritance | **Fixed** | Bug fix in V3Randomize.cpp |
| Coverpoint member access (.cp.get_coverage()) | **Fixed** | Bug fix in V3CoverageGroup.cpp |
| $bits for dynamic arrays/queues | **Works** | Already implemented |
| disable by task name | **Works** | Already implemented |
| randomize() with inline constraints | **Works** | Full UVM pattern support |
| Covergroup get_coverage()/get_inst_coverage() | **Works** | Returns correct values |
| foreach construct | **Works** | Standard iteration |
| Covergroup wildcard bins | **Works** | Pattern matching |
| Covergroup ignore_bins | **Works** | Coverage exclusion |
| do-while randomization pattern | **Works** | UVM `uvm_do` support |
| Cross coverage | **Works** | Full cross bin support |
| super keyword | **Works** | Parent method calls in classes |
| extern function | **Works** | Out-of-body class method definitions |
| modport export | **Works** | Interface function export to modules |
| stream operators on class members | **Works** | `{>> {p.data, p.addr}}` works |
| Multiplication in constraints | **Fixed** | `b == a * 2` now works in constraints |
| Division/modulo in constraints | **Works** | `b == a / 2`, `b == a % 10` work |
| Bitwise ops in constraints | **Works** | AND, OR, XOR work in constraints |
| Shift ops in constraints | **Works** | `<<`, `>>` work in constraints |
| constraint_mode() | **Works** | Enable/disable constraints at runtime |
| solve before | **Works** | Generates warning but constraint works |
| unique constraint with ranges | **Fixed** | Bug fix in constraint expansion |
| Implication constraints (->) | **Works** | `a > 0 -> b > a` works correctly |
| if-else constraints | **Works** | Conditional constraints work |
| Distribution constraints (dist) | **Works** | Weighted distribution works |
| Soft constraints | **Works** | Soft constraints with overrides |
| Nested class randomization | **Works** | rand class members work |
| Fixed array randomization | **Works** | foreach constraints work correctly |
| Queue/dynamic array size constraints | **Works** | size() constraints work |
| rand_mode() | **Works** | Enable/disable per-variable randomization |
| inside constraint | **Works** | Value set membership works |
| Packed struct randomization | **Works** | Constraints on struct fields work |
| Enum array randomization | **Works** | rand enum arrays with constraints |
| std::randomize() | **Works** | Global randomize with inline constraints |
| $cast function | **Works** | Runtime type checking and downcasting |
| Associative arrays (string keys) | **Works** | exists(), delete(), foreach work |
| $urandom/$urandom_range | **Works** | Random number generation |
| Virtual interfaces | **Works** | vif.signal, vif.clocking work |
| Mailbox | **Works** | put/get/try_get/peek/num work |
| Semaphore | **Works** | get/put/try_get work |
| Clocking blocks | **Works** | Clocking drives and samples work |

### Known Limitations

| Feature | Status | Workaround |
|---------|--------|------------|
| randc | Converted to rand | Possible duplicates |
| $psprintf with class args | Limited | Use $sformatf instead |

### AVIP Test Results (mbits-mirafra)

| AVIP | Test | Result |
|------|------|--------|
| APB | apb_8b_write_test | Full UVM phases complete |
| AXI4 | axi4_blocking_incr_burst_write_test | Transactions complete |
| SPI | SpiSimpleFdCpol0Cpha1Test | 5/5 comparisons pass, 25% coverage |
| UART | UartBaudRate9600Test | TX/RX assertions pass |
| AHB | AhbBaseTest | Basic test works |
| JTAG | JtagBaseTest | Compiles and runs |
| I2S | I2sBaseTest | Compiles and runs |
| I3C | I3cBaseTest | Compiles and runs |

