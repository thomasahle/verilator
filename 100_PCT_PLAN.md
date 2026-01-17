# Verilator sv-tests 100% Pass Plan

## Current Status (Updated 2026-01-17)

**sv-tests Analysis:**
- Total tests: 729
- Passing: 611/729 (84%)
- Failing: 118 (mostly UVM-dependent using different UVM)
- Truly non-UVM failures: ~17

**UVM Status:** uvm-core 2020 lints and simulates
**VIP Status:** All mbits-mirafra VIPs simulate successfully (APB, SPI tested)

### Recent Fixes (This Session)
- **Streaming concat with dynamic arrays** (IEEE 1800-2017 11.4.14) - Added E_UNSUPPORTED warning for dynamic arrays/queues inside streaming concatenation (e.g., `{<<8{header, len, data_arr}}`). Previously generated broken C++ code.
- **Sequence match items in properties** (IEEE 1800-2017 16.10) - Fixed AstSeqMatchItem transformation in V3AssertProp for constructs like `(valid, x = in) |-> ##4 (out == x + 4)`
- **$root hierarchical references** (IEEE 1800-2017 23.3.1) - $root standalone and $root.module.instance paths
- **Cell-as-value handling** - hierarchical scope references in function arguments
- **Coverage database functions** (IEEE 1800-2017 21.8) - $get_coverage, $load_coverage_db, $set_coverage_db_name stubs
- **Tagged union member types** (IEEE 1800-2017 7.3.2) - refined to allow only struct/union members, correctly reject real/string/chandle/event/class
- **Tagged union struct members** (IEEE 1800-2017 7.3.2) - allow unpacked struct/union members
- **Coverage system functions** (IEEE 1800-2017 21.8) - stub implementations ($coverage_control, etc)
- **Tagged unions/matches** - verified fully working
- **Repeat event control** - runtime fix, test now executes
- Sequence local variables with static lifetime
- Clocked sequences after local declarations
- Sequence clocking propagation to assertions
- Wide streaming ops with dynamic arrays (V3Premit fix)
- Sequence in event control (SEQEVENT warning)
- Procedural expect with clocking events
- t_delay_var regression fix (V3Timing fork wrapper)
- wait_order statement runtime support
- Non-blocking event triggers in tasks
- case...matches variable binding patterns
- **super keyword** (IEEE 1800-2023 8.15) - Parent class method calls
- **randomize(null)** (IEEE 1800-2017 18.7) - No-variable randomization
- **extends (default)** (IEEE 1800-2023) - Class inheritance with default constructor args
- **new(default)** (IEEE 1800-2023) - Constructor call with default arguments
- **matches in ternary** (IEEE 1800-2017) - Fixed precedence: `val matches tagged X ? 1 : 0` now works

### Known Issues (Needs Investigation)
- None currently

## Executive Summary

Achieving 100% on sv-tests requires implementing approximately 86 failing tests across 8 major feature categories. This plan prioritizes by impact, effort, and alignment with Verilator's simulation focus. Some features (tristate, strength modeling) are low-priority as they're primarily for gate-level simulation, not Verilator's RTL simulation target.

---

## Phase 1: Quick Wins (Est. 20+ tests, Low Effort)

### 1.1 Wildcard Equality Operators (11.4.6)
**Gap:** 11 failures (7/18 passing)
**Files:** `src/V3Const.cpp`, `src/V3Width.cpp`

The `==?` and `!=?` operators with X/Z wildcards need consistent handling:
- Issue: Some edge cases with mixed X/Z patterns fail
- Fix: Extend `AstEqWild`/`AstNeqWild` evaluation in constant folding
- Test: `tests/chapter-11/` wildcard tests

```cpp
// In V3Const.cpp, ensure proper wildcard matching:
// ==? treats X/Z in RHS as wildcards (don't care)
// Current implementation may miss edge cases
```

### 1.2 Equality Operators with X/Z (11.4.5)
**Gap:** ~7 failures
**Files:** `src/V3Const.cpp`

4-state equality (`===`, `!==`) vs 2-state equality (`==`, `!=`) behavior:
- Ensure `===` properly compares X and Z bits
- Ensure `==` returns X when comparing unknown values

### 1.3 White Space and Comments (5.3, 5.4)
**Gap:** ~6 failures each
**Files:** `src/verilog.l`, `src/V3PreProc.cpp`

Lexer handling of edge cases:
- Block comments with embedded special characters
- White space in macro expansions
- Likely preprocessor-related

---

## Phase 2: Medium Effort (Est. 30+ tests)

### 2.1 Continuous Assignment Strengths (10.3.4)
**Gap:** 8 failures (16/24 passing)
**Files:** `src/verilog.y`, `src/V3Strength.cpp` (new)

Strength specifications on continuous assignments:
```verilog
assign (strong0, weak1) out = a & b;
```

**Implementation:**
1. Parse strength specifiers (already parsed, marked BBUNSUP)
2. Store strength in AST nodes
3. Apply during simulation for conflicting drivers
4. Note: Low priority for RTL simulation use cases

### 2.2 User-Defined Nettypes (6.6.7)
**Gap:** 2+ failures
**Files:** `src/verilog.y:2460-2478`
**Status:** Currently BBUNSUP

```verilog
nettype real real_net;
nettype T mynet with resolution_func;
```

**Implementation:**
1. Remove BBUNSUP from nettype declarations
2. Create `AstNettype` node type
3. Handle resolution function linking
4. Implement net type checking

### 2.3 Tagged Unions and Matches Operator (11.9, 7.3.2)
**Status:** ✅ COMPLETE
**Files:** `src/verilog.y`, `src/V3Width.cpp`, `src/V3Match.cpp`

```verilog
typedef union tagged {
    void Invalid;
    int Valid;
} MaybeInt;

MaybeInt x = tagged Valid(42);
if (x matches tagged Valid .v) ...
```

All tagged union tests pass. Features working:
- `tagged` union type declarations
- `tagged` expression constructors
- `matches` pattern matching in if/case
- Variable binding in patterns (`.v`)
- Unpacked struct/union members allowed per IEEE 1800-2017 7.3.2
- Correctly rejects non-packable members (real, string, chandle, event, class)

### 2.4 Coverage System Functions (IEEE 1800-2017 21.8)
**Status:** ✅ COMPLETE (stub implementation)
**Files:** `src/V3AstNodeExpr.h`, `src/verilog.y`, `src/V3Width.cpp`, `src/V3EmitCFunc.h`

All coverage system functions implemented as stubs:
- `$coverage_control()` ✅ - returns 0
- `$coverage_get_max()` ✅ - returns 0
- `$coverage_get()` ✅ - returns 0.0
- `$coverage_merge()` ✅ - returns 0
- `$coverage_save()` ✅ - returns 0
- `$get_coverage()` ✅ - returns 0.0
- `$load_coverage_db()` ✅ - no-op
- `$set_coverage_db_name()` ✅ - no-op

Tests: `test_regress/t/t_coverage_funcs.py`, `test_regress/t/t_coverage_funcs2.py`

---

## Phase 3: Complex Features (Est. 20+ tests)

### 3.1 Tristate Net Types (tri0, tri1, trireg)
**Gap:** 3+ failures
**Files:** `src/V3Tristate.cpp`
**Priority:** LOW (gate-level feature)

```verilog
tri0 net1;  // Pulls to 0 when undriven
tri1 net2;  // Pulls to 1 when undriven
trireg net3; // Holds last driven value
```

Current V3Tristate.cpp has 25+ BBUNSUP items. These are gate-level modeling features rarely used in RTL simulation.

**Recommendation:** Document as out-of-scope for RTL simulation, or implement basic pull behavior without full strength modeling.

### 3.2 Unresolved Net Types (6.6.2)
**Gap:** 1 failure
**Files:** `src/verilog.y`, `src/V3LinkResolve.cpp`

```verilog
uwire net1;  // Error if multiple drivers
```

**Implementation:**
1. Parse `uwire` declarations
2. Check for multiple drivers during elaboration
3. Generate error if multiply driven

### 3.3 Interconnect Nets (6.6.8)
**Gap:** Likely included in net failures
**Files:** `src/verilog.y:1387,1821`
**Status:** BBUNSUP

```verilog
interconnect net1;
```

Generic interconnect for mixed-signal. Low priority for digital RTL.

---

## Phase 4: Edge Cases and Refinements

### 4.1 Real Data Type Edge Cases (6.12)
**Gap:** ~3 failures

Floating-point edge cases:
- Infinity handling
- NaN comparisons
- Real-to-integer conversion edge cases

### 4.2 Keywords and Reserved Words (5.6.2)
**Gap:** 2 failures

Likely related to:
- Context-sensitive keywords
- Future reserved words
- Escaped identifier edge cases

### 4.3 Net Declaration Edge Cases (6.5)
**Gap:** 2 failures

Variable vs net declaration contexts in:
- Interface ports
- Modport expressions
- Generate blocks

---

## Implementation Priority Matrix

| Feature | Tests | Effort | Priority | Notes |
|---------|-------|--------|----------|-------|
| Wildcard Equality | 11 | Low | HIGH | Core operator |
| Equality X/Z | 7 | Low | HIGH | Core operator |
| White Space/Comments | 12 | Low | MEDIUM | Lexer fixes |
| Strength Specs | 8 | Medium | LOW | Gate-level |
| User Nettypes | 2 | Medium | MEDIUM | Clean feature |
| Tagged Unions | 3 | High | MEDIUM | Pattern matching |
| Coverage Functions | 1 | Medium | HIGH | Testbench utility |
| Tristate Nets | 3 | High | LOW | Gate-level |
| Real Edge Cases | 3 | Low | MEDIUM | Math fixes |

---

## Recommended Implementation Order

### Sprint 1: Core Operators (Est. 25 tests)
1. Fix wildcard equality edge cases
2. Fix 4-state equality handling
3. Add missing coverage functions

### Sprint 2: Parsing/Lexer (Est. 15 tests)
1. Fix white space handling
2. Fix comment edge cases
3. Fix keyword recognition

### Sprint 3: Type System (Est. 10 tests)
1. Implement user-defined nettypes
2. Implement `uwire` declarations
3. Fix real number edge cases

### Sprint 4: Advanced Features (Est. 10 tests)
1. Implement tagged unions
2. Implement `matches` operator
3. Net declaration edge cases

### Sprint 5: Gate-Level (Optional, 26 tests)
1. Strength specifications
2. tri0/tri1 pull behavior
3. trireg charge storage

---

## Files to Modify

| File | Changes | Sprint |
|------|---------|--------|
| `src/V3Const.cpp` | Wildcard/equality evaluation | 1 |
| `src/V3Width.cpp` | Type checking fixes | 1,3 |
| `src/verilated_cov.cpp` | Coverage functions | 1 |
| `src/verilog.l` | Lexer edge cases | 2 |
| `src/V3PreProc.cpp` | Preprocessor fixes | 2 |
| `src/verilog.y` | Remove BBUNSUP, add nettypes | 3 |
| `src/V3LinkResolve.cpp` | Nettype resolution | 3 |
| `src/V3Ast*.h` | New AST nodes for tagged unions | 4 |
| `src/V3Tristate.cpp` | Gate-level support | 5 |

---

## Testing Strategy

1. **Run sv-tests locally:**
   ```bash
   cd ~/repos/sv-tests
   PATH=~/repos/verilator/bin:$PATH make tests RUNNERS_FILTER=Verilator -j8
   ```

2. **Track specific failures:**
   ```bash
   grep -l "FAIL" out/logs/Verilator/**/*.log
   ```

3. **Add regression tests:**
   - For each fix, add corresponding test to `test_regress/t/`
   - Ensure Verilator's own test suite passes

---

## Risk Assessment

| Risk | Mitigation |
|------|------------|
| Strength modeling complexity | Accept partial support; document limitations |
| Tagged union performance | Use efficient union representation |
| Gate-level test expectations | Clarify RTL vs gate-level scope |
| Backward compatibility | Ensure existing designs still work |

---

## Success Metrics

- **Goal:** 1610/1610 tests (100%)
- **Stretch:** Add 50+ new Verilator regression tests
- **Validation:** All existing Verilator tests still pass

---

## Phase 6: UVM-Specific Enhancements

### 6.1 UVM Core Status
**Status:** uvm-core 2020 lints and simulates
**Location:** `/Users/ahle/repos/verilator/include/uvm_pkg.sv`

### 6.2 Factory & Registry
- Type registration works
- Factory overrides functional
- TODO: Performance optimization for large registries

### 6.3 Phasing System
- All standard phases execute correctly
- run_test() initiates properly
- TODO: Phase jump/skip, domain-specific phases

### 6.4 TLM & Messaging
- Basic TLM ports work
- uvm_info/warning/error/fatal work
- TODO: Analysis port performance, message filtering

### 6.5 Config DB
- Works with timing fixes (added #0 delay)
- TODO: Hierarchical wildcard matching optimization

### 6.6 Randomization Integration
- UVM sequences can randomize
- std::randomize() functional
- TODO: Constraint debugging, rand_mode/constraint_mode

---

## Phase 7: SVA Property Operators (Chapter 16)

### 7.1 Currently Working
- Implication (`|->`, `|=>`)
- Cycle delays (`##n`, `##[n:m]`)
- Repetition (`[*n]`, `[*n:m]`)
- Boolean operators

### 7.2 Needed for Full Compliance
- `accept_on` / `reject_on`
- `sync_accept_on` / `sync_reject_on`
- `nexttime` / `s_nexttime`
- `always` / `s_always`
- `eventually` / `s_eventually`
- Sequence method calls (.triggered, .matched)

---

## Appendix: Feature Status (Updated Jan 2026)

### Now Working (Verified Jan 2026)
The following features were previously listed as unsupported but are now verified working:

**SVA/Assertions (all working):**
- `&&&` level-sensitive event control ✓
- `repeat event control` ✓
- `#-#` and `#=#` operators ✓
- `accept_on`, `reject_on`, `sync_accept_on`, `sync_reject_on` ✓
- `nexttime`, `s_nexttime`, `s_always`, `s_eventually` ✓
- `[*]`, `[+]`, `[=]`, `[->]` sequence repetition ✓
- Property case expressions ✓
- Sequence match items ✓
- Property/sequence local variables ✓

**Type System (working):**
- Tagged unions ✓
- `matches` operator ✓
- Extern task/function ✓

**Class Features (working):**
- `super` keyword for parent method calls ✓
- `randomize(null)` for no-variable randomization ✓
- `extends BaseClass(default)` for default constructor args ✓
- `super.new(default)` for default parent constructor args ✓

**LOW (still unsupported, rarely used):**
- User-defined nettypes
- Strength specifications
- Tristate pull types
- Checker constructs
- `function new(default)` declaration-side default (inherits constructor interface)
- Clocking event edge override in clocking blocks
