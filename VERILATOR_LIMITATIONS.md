# Verilator Limitations for Xcellium Compatibility

This document lists SystemVerilog features that work in Xcellium (Cadence) but are unsupported or limited in Verilator.

## SVA (SystemVerilog Assertions)

| Feature | Status | Notes |
|---------|--------|-------|
| Sequence operators (`##`, `##[n:m]`) | ❌ Unsupported | Cycle delay operators in sequences |
| `s_until`, `s_until_with` | ❌ Unsupported | Strong until operators |
| `throughout` | ❌ Unsupported | Throughout operator |
| `within` | ❌ Unsupported | Within operator |
| `intersect` | ❌ Unsupported | Sequence intersection |
| `first_match` | ❌ Unsupported | First match operator |
| Multi-cycle assertions | ❌ Unsupported | Only single-cycle assertions work |
| SEREs (Sequential Extended Regular Expressions) | ❌ Unsupported | Complex sequence patterns |
| Unclocked assertions | ❌ Unsupported | Assertions without clock |
| Recursive property calls | ❌ Unsupported | Properties calling themselves |
| `$assertcontrol` | ⚠️ Limited | Only some control types supported |
| Procedural concurrent assertions | ⚠️ Limited | Limited support |

## Timing and Synchronization

| Feature | Status | Notes |
|---------|--------|-------|
| Writing to inout in fork after timing | ❌ Unsupported | "Writing to a captured inout variable in a fork after a timing control" |
| `disable fork` from task/function | ❌ Unsupported | Must be in same scope |
| `disable` task by name | ❌ Unsupported | Only block disable supported |
| Rising/falling/turn-off delays | ❌ Unsupported | Only typical delays |
| Min/typ/max delays | ⚠️ Limited | Only typical value used |
| `#0` delays | ⚠️ Different | Works differently than LRM |
| `@*` in some contexts | ❌ Unsupported | "Unsupported: no sense equation (@*)" |

## Classes and OOP

| Feature | Status | Notes |
|---------|--------|-------|
| `super` keyword | ❌ Unsupported | Cannot use super in some contexts |
| Virtual interfaces | ❌ Unsupported | Not implemented |
| `randomize with (...)` on object | ❌ Unsupported | `obj.randomize with {...}` limited |
| `randomize(null)` | ❌ Unsupported | Null argument not supported |
| `rand_mode()` on static variables | ❌ Unsupported | Only instance variables |
| Class handle comparisons | ⚠️ Limited | Some comparison operations limited |

## Interfaces and Modports

| Feature | Status | Notes |
|---------|--------|-------|
| Virtual interfaces | ❌ Unsupported | Not implemented |
| Unnamed interfaces | ❌ Unsupported | Must be named |
| Generate blocks around modports | ❌ Unsupported | Modports must be static |
| Modport exports | ❌ Unsupported | Only imports supported |
| Interface slices | ❌ Unsupported | `iface[a:b]` not supported |
| Interface on top-level ports | ❌ Unsupported | Can't have interface port on top module |
| Multidimensional interfaces | ❌ Unsupported | Single dimension only |

## Randomization and Constraints

| Feature | Status | Notes |
|---------|--------|-------|
| `randsequence` under `randsequence` | ❌ Unsupported | No nested randsequence |
| Randsequence production function variables | ❌ Unsupported | Limited production support |
| Randsequence production function ports | ❌ Unsupported | Limited production support |
| `$urandom` per-object stability | ⚠️ Different | One seed per thread, not per object |
| `$random` per-module stability | ⚠️ Different | One seed per thread, not per module |

## Coverage

| Feature | Status | Notes |
|---------|--------|-------|
| Cross coverage < 2 coverpoints | ❌ Unsupported | Need at least 2 coverpoints |
| `cover` with some rep types | ⚠️ Ignored | Some coverage types ignored |
| Coverage with `--savable` | ❌ Unsupported | Not supported together |

## Expressions and Operators

| Feature | Status | Notes |
|---------|--------|-------|
| `++`/`--` in some contexts | ⚠️ Limited | Only as standalone statements or limited cases |
| Cast to non-basic types | ❌ Unsupported | Only scalar types supported |
| Size-changing cast on complex types | ❌ Unsupported | Only basic types |
| `$bits` for dynamic array | ❌ Unsupported | Not supported |
| `$bits` for queue | ❌ Unsupported | Not supported |
| `$c` > 64 bits | ❌ Unsupported | Max 64-bit output |
| 4-state numbers in some contexts | ❌ Unsupported | 2-state simulator |
| Slice with non-constant bounds | ❌ Unsupported | Must be constant |
| `case inside` | ❌ Unsupported | Use regular case |
| `case matches` | ❌ Unsupported | Pattern matching case |
| `inside` with `$` bound | ❌ Unsupported | Upper bound limitation |

## Modules and Hierarchy

| Feature | Status | Notes |
|---------|--------|-------|
| Hierarchical config rules | ❌ Unsupported | Config blocks limited |
| Bind to instance path | ❌ Unsupported | Only bind to module name |
| `defparam` with generate arrays | ❌ Unsupported | `defparam inst[i].param` fails |
| Per-bit array instantiations | ❌ Unsupported | Array instances limited |

## Gate Primitives

| Feature | Status | Notes |
|---------|--------|-------|
| 3-state gate primitives | ❌ Unsupported | `cmos`, `tran`, etc. |
| MOS gate primitives | ❌ Unsupported | `nmos`, `pmos` limited |

## Force/Release

| Feature | Status | Notes |
|---------|--------|-------|
| Force with procedural continuous assign | ❌ Unsupported | Treated as procedural |
| Force with dependent variable refs | ⚠️ Limited | Uses initial value |
| Multi-variable force expressions | ⚠️ Limited | Not sensitive to changes |

## Misc SystemVerilog

| Feature | Status | Notes |
|---------|--------|-------|
| `shortreal` | ⚠️ Converted | Converted to `real` |
| `uwire` checking | ⚠️ Ignored | Treated as `wire` |
| `checker` | ⚠️ Limited | Treated as `module` |
| `chandle` | ⚠️ Limited | Treated as `longint` |
| Specify blocks | ❌ Ignored | Timing checks ignored |
| `%m` in `$fscanf` | ❌ Unsupported | Module path in fscanf |
| `%l` in `$fscanf` | ❌ Unsupported | Library in fscanf |
| Public functions > 64-bit output | ❌ Unsupported | Max 64-bit public output |
| `no_inline` for tasks | ❌ Unsupported | Tasks always inlined |
| Encrypted Verilog (P1735) | ❌ Unsupported | Cannot decrypt IP |

## Two-State vs Four-State

| Feature | Status | Notes |
|---------|--------|-------|
| `===` / `!==` with variables | ⚠️ Different | Converted to `==`/`!=` |
| X propagation | ⚠️ Different | X converted to constant |
| Z propagation | ⚠️ Limited | Only simple tristate supported |
| Initial X values | ⚠️ Different | Randomized or constant |

## Structures and Unions

| Feature | Status | Notes |
|---------|--------|-------|
| Mixed blocking/non-blocking in struct | ❌ Unsupported | Must be consistent |

## Encountered in AVIP Testing

| Feature | AVIP | Notes |
|---------|------|-------|
| `##` sequence operators | AHB | Assertions use `##1`, `##[1:$]` |
| Inout fork timing writes | I3C | BFM writes inout in forked task after timing |
| `s_until_with` | AXI4 | Some assertion files use this |

---

## Workarounds

### For SVA Sequences
Remove or comment out complex assertions using `##`, `s_until_with`, etc. Use simple single-cycle assertions.

### For Inout Fork Timing
Refactor code to not write to inout variables from inside fork blocks after timing controls. Use local variables and assign outside the fork.

### For Virtual Interfaces
Use regular interfaces with modports instead of virtual interfaces.

### For Encrypted IP
Request unencrypted RTL from vendor or use `--protect-lib` for your own IP.

---

*Last updated: 2025-12-29*
