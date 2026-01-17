# Verilator E_UNSUPPORTED Feature List

Generated: January 14, 2026
Based on analysis of src/*.cpp and src/verilog.y

## Summary

| Category | Count | Priority |
|----------|-------|----------|
| Parser (BBUNSUP) | 107 | Mixed |
| Tristate | 25 | LOW |
| Constraints/Randomize | 12 | MEDIUM |
| Type System/Casts | 15 | MEDIUM |
| Assertions/SVA | 20 | MEDIUM |
| Tasks/Functions | 8 | MEDIUM |
| Timing/Scheduling | 6 | MEDIUM |
| Coverage | 5 | LOW |
| Other | 20+ | LOW |

---

## HIGH PRIORITY (Commonly Used)

### 1. ~~`&&& expression` (Level-Sensitive Event Control)~~ ✓ NOW SUPPORTED
- **Status:** WORKS - see test_regress/t/t_event_andandand.v
- **Syntax:** `@(posedge clk &&& enable)`
- **Verified:** January 2026

### 2. ~~`repeat event control`~~ ✓ NOW SUPPORTED
- **Status:** WORKS - see test_regress/t/t_repeat_event_control.v, t_timing_repeat_event.v
- **Syntax:** `repeat (n) @(posedge clk)`
- **Verified:** January 2026

### 3. Inline constraints with `randomize with (...) {...}`
- **File:** V3LinkDot.cpp:1988
- **Note:** Basic inline constraints work; complex patterns may not

### 4. ~~`super` keyword~~ ✓ NOW SUPPORTED
- **Status:** WORKS - see test_regress/t/t_class_super.v
- **Note:** Calling parent class methods explicitly
- **Verified:** January 2026

### 5. `$cast` to certain types
- **File:** V3Width.cpp:2519, 2548, 2575
- **Note:** Some cast targets unsupported

---

## MEDIUM PRIORITY (Less Common)

### Assertions/SVA

| Feature | File:Line | Notes |
|---------|-----------|-------|
| ~~`#-#` non-overlapping followed-by~~ | verilog.y:6951 | ✓ NOW SUPPORTED (maps to `\|->`) |
| ~~`#=#` non-overlapping followed-by~~ | verilog.y:6953 | ✓ NOW SUPPORTED (maps to `\|=>`) |
| ~~`accept_on`~~ | verilog.y:6990 | ✓ NOW SUPPORTED (property expression) |
| ~~`reject_on`~~ | verilog.y:6992 | ✓ NOW SUPPORTED (property expression) |
| ~~`sync_accept_on`~~ | verilog.y:6995 | ✓ NOW SUPPORTED (property expression) |
| ~~`sync_reject_on`~~ | verilog.y:6997 | ✓ NOW SUPPORTED (property expression) |
| ~~`nexttime`/`s_nexttime`~~ | verilog.y:6956-6961 | ✓ NOW SUPPORTED |
| ~~`s_always`~~ | verilog.y:6967 | ✓ NOW SUPPORTED |
| ~~`s_eventually`~~ | verilog.y:6969-6973 | ✓ NOW SUPPORTED |
| ~~`[*]`/`[*n]` consecutive repetition~~ | verilog.y:7042-7043 | ✓ NOW SUPPORTED |
| ~~`[+]` one-or-more repetition~~ | verilog.y:7044-7045 | ✓ NOW SUPPORTED |
| ~~`[=n]` non-consecutive repetition~~ | verilog.y:7047-7049 | ✓ NOW SUPPORTED |
| ~~`[->n]` goto repetition~~ | verilog.y:7032-7035 | ✓ NOW SUPPORTED |
| ~~Property/sequence local variables~~ | verilog.y:6649-6763 | ✓ NOW SUPPORTED (see t_assert_seq_local.v) |
| ~~Property case expression~~ | verilog.y:6871-6886 | ✓ NOW SUPPORTED (AstPropCase) |
| ~~Sequence match items~~ | verilog.y:6792 | ✓ NOW SUPPORTED (Jan 2026) |

### Constraints

| Feature | File:Line | Notes |
|---------|-----------|-------|
| `default :/` constraint | verilog.y:7953 | Distribution constraint |
| `constraint_mode()` on static | V3Randomize.cpp:404 | Static variable rand_mode |
| `randomize(null)` | V3Width.cpp:4806 | Randomize with null |
| Complex constraint expressions | V3Randomize.cpp:817, 1190 | Some expressions unsupported |

### Type System

| Feature | File:Line | Notes |
|---------|-----------|-------|
| ~~Tagged unions~~ | verilog.y:2106, 2278, 3936-3942 | ✓ NOW SUPPORTED |
| ~~`matches` operator~~ | verilog.y:5153-5155, 3584 | ✓ NOW SUPPORTED |
| Nettype declarations | verilog.y:2460-2478 | User-defined net types |
| Size-changing cast on non-basic | V3Width.cpp:2713 | Cast limitations |

### Tasks/Functions

| Feature | File:Line | Notes |
|---------|-----------|-------|
| ~~Extern task/function~~ | verilog.y:1801-1807 | ✓ NOW SUPPORTED (see t_class_extern.v) |
| Out of block function decl | verilog.y:4658, 4726 | Forward declarations |
| `no_inline` for tasks | V3Control.cpp:903 | Inlining control |
| Disabling fork from task | V3LinkJump.cpp:232 | Fork control |

---

## LOW PRIORITY (Rarely Used)

### Strength Specifiers
- **Files:** verilog.y:71, 5772-5797
- Gate strength, highz strength, pullup/pulldown strength
- Only relevant for analog/gate-level simulation

### Tristate (25+ items in V3Tristate.cpp)
- Complex tristate constructs
- Top-level tristate IO
- Tristate port expressions
- Only relevant for FPGA/ASIC gate-level

### Clocking
| Feature | File:Line | Notes |
|---------|-----------|-------|
| Default clocking identifier | verilog.y:2727 | Default block reference |
| ~~Clocking edge override~~ | verilog.y:6536-6544 | ✓ NOW WARNS (posedge/negedge/edge in clocking skew) |

### Config/Library
| Feature | File:Line | Notes |
|---------|-----------|-------|
| Config use parameter | verilog.y:8109-8111 | Configuration |
| Config incdir/include | verilog.y:8130-8133 | Library paths |
| Hierarchical config rule | V3LinkCells.cpp:190 | Config rules |

### Other
| Feature | File:Line | Notes |
|---------|-----------|-------|
| ~~`wait_order`~~ | verilog.y:3721-3725 | ✓ NOW SUPPORTED (Jan 2026) |
| `expect` | verilog.y:3738-3742 | Expect statement |
| Checker constructs | verilog.y:1123, 7530-7533 | Checker keyword |
| `deassign` | verilog.y:3570 | Verilog 1995 |
| `trireg` | verilog.y:1863 | Net type |
| `interconnect` | verilog.y:1387, 1821 | SystemVerilog |
| Programs within modules | verilog.y:2625 | Program blocks |
| Modules within modules | verilog.y:2627 | Nested modules |
| Interface within interface | verilog.y:1541 | Nested interfaces |

---

## Implementation Recommendations

### Phase 1: Quick Wins ✅ MOSTLY COMPLETE
1. ~~**`&&& expression`** - Level-sensitive event control~~ ✓ ALREADY WORKS
2. ~~**`repeat event control`**~~ ✓ ALREADY WORKS
3. ~~**`#-#` and `#=#` assertion operators**~~ ✓ ALREADY WORKS
4. ~~**Property case expressions**~~ ✓ ALREADY WORKS
5. **`$countbits` with 4+ fields** (verilog.y:4401) - needs extending

### Phase 2: Medium Effort ✅ MOSTLY COMPLETE
1. ~~**Property/sequence local variables**~~ ✓ ALREADY WORKS

### Phase 3: Complex/Low Value
1. Tristate constructs
2. ~~Tagged unions/matches~~ ✓ ALREADY WORKS
3. Nettype declarations
4. Checker constructs

---

## Files Reference

| File | Purpose |
|------|---------|
| src/verilog.y | Parser - BBUNSUP macro usage |
| src/V3Tristate.cpp | Tristate handling |
| src/V3Randomize.cpp | Constraint randomization |
| src/V3Width.cpp | Type resolution and casting |
| src/V3Assert.cpp | Assertion processing |
| src/V3AssertPre.cpp | Assertion preprocessing |
| src/V3LinkDot.cpp | Symbol table and linking |
| src/V3Task.cpp | Task/function processing |
| src/V3Timing.cpp | Timing control |

---

## Notes

- **BBUNSUP** = "Build But Unsupported" - parsed but generates error
- **E_UNSUPPORTED** = General unsupported error code
- Many items are rarely used edge cases
- Tristate items are gate-level features (not needed for UVM)
- Most UVM testbenches work fine without these features
