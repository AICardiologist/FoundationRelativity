# CRITICAL: Infrastructure Lemma Failures - November 2, 2025

**Date**: November 2, 2025
**Build**: `build_clean_fresh_nov1.txt` (full clean rebuild, 3085 modules)
**Total Errors**: 15 compilation errors
**Infrastructure Errors**: 2 (lines 1745, 1761)
**Status**: 🔴 **CRITICAL FAILURE** - Paul's fixes did not work

---

## Executive Summary

After a complete clean rebuild (`lake clean`), **Paul's three infrastructure lemma fixes FAILED**:

1. ✅ `g_offdiag_zero` (line 1733): **Compiles successfully** with Paul's fix
2. ❌ `insert_delta_right_diag` (line 1745): **UNSOLVED GOALS** - Paul's simp hints didn't work
3. ❌ `insert_delta_left_diag` (line 1761): **UNSOLVED GOALS** - Paul's simp hints didn't work

**Root Cause**: The explicit AC lemmas (`mul_assoc, mul_left_comm, mul_comm, mul_zero, zero_mul`) added to the `simp` call are NOT closing the goal in the off-diagonal case.

---

## Error Summary

### Infrastructure Errors (2)
1. **Line 1745**: `unsolved goals` in `insert_delta_right_diag` off-diagonal branch
2. **Line 1761**: `unsolved goals` in `insert_delta_left_diag` off-diagonal branch

### Block A Errors (2)
3. **Line 8733**: `unexpected token 'have'; expected 'lemma'`
4. **Line 8948**: `unexpected token 'have'; expected 'lemma'`

### Other Errors (11)
- Line 2341: Type mismatch
- Line 3077: unsolved goals
- Line 6049: unsolved goals
- Line 7501: unsolved goals
- Line 7803: unsolved goals
- Line 8605: unsolved goals
- Line 8070: unsolved goals
- Line 9362: Tactic rewrite failed
- Line 9428: unsolved goals
- Line 9495: Type mismatch
- Line 9533: unsolved goals

---

## Critical Finding: Paul's Fixes Applied But Don't Work

### What Was Applied (Verified)

**Line 1733** - `g_offdiag_zero`:
```lean
@[simp] lemma g_offdiag_zero (M r θ : ℝ) {i j : Idx} (h : i ≠ j) :
  g M i j r θ = 0 := by
  cases i <;> cases j <;> (first | exact (False.elim (h rfl)) | simp [g])
```
**Status**: ✅ **COMPILES** (no error at line 1733)

**Line 1749** - `insert_delta_right_diag` (off-diagonal case):
```lean
·
  have hz : g M ρ b r θ = 0 := g_offdiag_zero M r θ h
  -- With ρ ≠ b we have (if ρ=b then 1 else 0) = 0, and g_{ρb}=0.
  -- Force both sides to literal 0.
  simp [hz, h, mul_assoc, mul_left_comm, mul_comm, mul_zero, zero_mul]
```
**Status**: ❌ **FAILS** with `unsolved goals` at line 1745

**Line 1763** - `insert_delta_left_diag` (off-diagonal case):
```lean
·
  have hz : g M a ρ r θ = 0 := g_offdiag_zero M r θ (ne_comm.mpr h)
  simp [hz, h, mul_assoc, mul_left_comm, mul_comm, mul_zero, zero_mul]
```
**Status**: ❌ **FAILS** with `unsolved goals` at line 1761

---

## Analysis: Why Paul's Fix Didn't Work

### The Goal State

After `by_cases h : ρ = b`, the off-diagonal branch has:
- **Hypothesis**: `h : ρ ≠ b`
- **Goal**: `F ρ * g M ρ b r θ = F ρ * g M ρ b r θ * (if ρ = b then 1 else 0)`

After `have hz : g M ρ b r θ = 0 := g_offdiag_zero M r θ h`:
- **Hypothesis**: `hz : g M ρ b r θ = 0`
- **Hypothesis**: `h : ρ ≠ b`
- **Goal**: `F ρ * g M ρ b r θ = F ρ * g M ρ b r θ * (if ρ = b then 1 else 0)`

**Expected** after `simp [hz, h, ...]`:
1. Replace `g M ρ b r θ` with `0` (using `hz`)
2. Replace `(if ρ = b then 1 else 0)` with `0` (using `h : ρ ≠ b` via `if_neg`)
3. Simplify `F ρ * 0 = F ρ * 0 * 0` to `0 = 0` (using `mul_zero, zero_mul`)

### Hypothesis: Missing `if_neg` Application

The `simp [h, ...]` might not automatically apply `if_neg : ¬P → (if P then a else b) = b`.

**Evidence**:
- `h : ρ ≠ b` is a negative hypothesis
- `simp` may not automatically use `if_neg h` to rewrite `(if ρ = b then 1 else 0)`
- The explicit AC lemmas might help with normalization but don't address the `if` expression

### Hypothesis: AC Lemma Performance Issue

Adding `mul_assoc, mul_left_comm, mul_comm` to `simp` might:
1. Cause non-termination or very slow performance
2. Not converge to `0 = 0` in the expected way
3. Create a rewrite loop

### Hypothesis: Syntax Issue

The syntax `simp [hz, h, mul_assoc, mul_left_comm, mul_comm, mul_zero, zero_mul]` might be:
1. Trying to use `h : ρ ≠ b` directly as a simp lemma (which doesn't work)
2. Missing an explicit `if_neg h` application
3. Not forcing Lean to unfold the `if_then_else` correctly

---

## Recommended Fixes

### Option A: Explicit `if_neg` Application
```lean
·
  have hz : g M ρ b r θ = 0 := g_offdiag_zero M r θ h
  simp [hz, if_neg h, mul_zero, zero_mul]
```

### Option B: Rewrite Instead of Simp
```lean
·
  have hz : g M ρ b r θ = 0 := g_offdiag_zero M r θ h
  rw [hz, if_neg h]
  simp [mul_zero, zero_mul]
```

### Option C: Explicit Ring Normalization
```lean
·
  have hz : g M ρ b r θ = 0 := g_offdiag_zero M r θ h
  rw [hz, if_neg h]
  ring
```

### Option D: Manual Calculation
```lean
·
  have hz : g M ρ b r θ = 0 := g_offdiag_zero M r θ h
  calc F ρ * g M ρ b r θ
      = F ρ * 0                                     := by rw [hz]
    _ = 0                                           := by rw [mul_zero]
    _ = 0 * 0                                       := by rw [zero_mul]
    _ = F ρ * 0 * 0                                 := by rw [mul_zero]
    _ = F ρ * g M ρ b r θ * 0                       := by rw [hz]
    _ = F ρ * g M ρ b r θ * (if ρ = b then 1 else 0) := by rw [if_neg h]
```

---

## Block A Errors

The two errors at lines 8733 and 8948 are in Block A (lines 8640-9100) with "unexpected token 'have'; expected 'lemma'".

This suggests a **syntax error** where a `have` statement is appearing at the top level instead of inside a proof.

**Hypothesis**: These might be related to the infrastructure lemma failures cascading into Block A.

---

## Next Steps

### Immediate Actions Required

1. **Test Option A**: Try adding `if_neg h` explicitly to the `simp` call
2. **Test Option B**: Try using `rw` instead of `simp` for the critical rewrites
3. **Test Option C**: Try using `ring` after rewriting
4. **Investigate Block A errors**: Check lines 8733 and 8948 for syntax issues

### Questions for Paul

1. **Q1**: Why didn't the explicit AC lemmas in `simp` close the goal?
2. **Q2**: Should we use `if_neg h` explicitly, or does `simp [h, ...]` handle it automatically?
3. **Q3**: Are there other missing simp lemmas needed for `if_then_else` expressions?
4. **Q4**: What is the expected tactic sequence for this proof?

---

## Build Evidence

**Full Clean Build**: `lake clean && lake build`
- **Compiled**: 3085 modules from scratch
- **Exit Code**: 0 (build succeeded syntactically)
- **Total Errors**: 15 compilation errors
- **Infrastructure Failures**: 2 (lines 1745, 1761)
- **Block A Failures**: 2 (lines 8733, 8948)

**Error Lines**:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:1745:2: unsolved goals
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:1761:2: unsolved goals
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:2341:2: Type mismatch: After simplification, term
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:3077:57: unsolved goals
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:6049:72: unsolved goals
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:7501:58: unsolved goals
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:7803:58: unsolved goals
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8605:65: unsolved goals
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8070:63: unsolved goals
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8733:76: unexpected token 'have'; expected 'lemma'
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8948:75: unexpected token 'have'; expected 'lemma'
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9362:6: Tactic `rewrite` failed: Did not find an occurrence of the pattern
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9428:65: unsolved goals
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9495:73: Type mismatch
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9533:57: unsolved goals
```

---

**Prepared by**: Claude Code (Lean 4 Assistant)
**Build**: `build_clean_fresh_nov1.txt` (full clean rebuild)
**Date**: November 2, 2025
**Status**: Infrastructure lemmas failing - Paul's fixes insufficient

---

**END OF CRITICAL DIAGNOSTIC**
