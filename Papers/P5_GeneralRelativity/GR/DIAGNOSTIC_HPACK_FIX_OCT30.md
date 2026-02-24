# Diagnostic: hpack Fix - Explicit Definition Unfolding - October 30, 2025

**Date**: October 30, 2025
**File**: Riemann.lean line 1774
**Status**: ⚙️ **FIX APPLIED** - Building...
**Build log**: `build_hpack_fix_oct30.txt`
**Previous error count**: 26 errors

---

## Executive Summary

After fixing the forward reference issue with `sumIdx_congr`, the build revealed a new error at line 1774 where `rfl` was failing to establish definitional equality. The issue was that `set` definitions (`f1`, `f2`, `f3`, `f4`) are not automatically unfolded by `rfl`.

**Solution**: Replace `rfl` with `simp only [f1, f2, f3, f4]` to explicitly unfold the local definitions.

---

## Error from Previous Build

```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:1774:4: Tactic `rfl` failed: The left-hand side
  -dCoord μ (fun r θ => g M e b r θ) r θ * Γtot M r θ e ν a + dCoord ν (fun r θ => g M e b r θ) r θ * Γtot M r θ e μ a -
      dCoord μ (fun r θ => g M a e r θ) r θ * Γtot M r θ e ν b +
    dCoord ν (fun r θ => g M a e r θ) r θ * Γtot M r θ e μ b
is not definitionally equal to the right-hand side
  f1 e + f2 e + f3 e + f4 e
```

---

## Root Cause Analysis

### The Problem

In JP's heartbeat-safe proof, step 2 defines local abbreviations using `set`:

```lean
set f1 : Idx → ℝ :=
  fun e => -(dCoord μ (fun r θ => g M e b r θ) r θ) * Γtot M r θ e ν a
set f2 : Idx → ℝ :=
  fun e =>  (dCoord ν (fun r θ => g M e b r θ) r θ) * Γtot M r θ e μ a
set f3 : Idx → ℝ :=
  fun e => -(dCoord μ (fun r θ => g M a e r θ) r θ) * Γtot M r θ e ν b
set f4 : Idx → ℝ :=
  fun e =>  (dCoord ν (fun r θ => g M a e r θ) r θ) * Γtot M r θ e μ b
```

Then the `hpack` step tries to show:

```lean
have hpack :
  (fun e =>
    -(dCoord μ ...) * Γtot ... + (dCoord ν ...) * Γtot ...
    - (dCoord μ ...) * Γtot ... + (dCoord ν ...) * Γtot ...)
  =
  (fun e => ((f1 e + f2 e) + f3 e) + f4 e) := by
  funext e
  rfl  -- ❌ FAILS HERE
```

**Issue**: Lean's `rfl` only works for **definitional equality**. The `set` command creates local definitions that are **not automatically unfolded** by `rfl`. Therefore, Lean cannot see that `f1 e`, `f2 e`, `f3 e`, `f4 e` are definitionally equal to their expanded forms.

### Why This Matters

JP's proof strategy relies on fixing the parenthesization to `(((f1+f2)+f3)+f4)` so that later splitting steps work correctly. The `hpack` step is supposed to establish that the explicit expansion matches this parenthesized form, but `rfl` cannot do this without explicitly unfolding the definitions.

---

## The Fix

**Changed line 1774**:
```lean
-- BEFORE:
    rfl

-- AFTER:
    simp only [f1, f2, f3, f4]
```

**Why this works**: `simp only` with the explicit list `[f1, f2, f3, f4]` tells Lean to unfold only these definitions and nothing else. After unfolding, the LHS and RHS become syntactically identical, and Lean can establish the equality.

**Key point**: This is still a "lightweight" operation as JP intended - we're not asking `simp` to do any AC normalization or other heavy work. We're just explicitly unfolding four local definitions.

---

## Code Location

**File**: Riemann.lean
**Lines 1764-1774**: The `hpack` step in `payload_split_and_flip` proof

**Full fixed code**:
```lean
have hpack :
  (fun e =>
    -(dCoord μ (fun r θ => g M e b r θ) r θ) * Γtot M r θ e ν a
    + (dCoord ν (fun r θ => g M e b r θ) r θ) * Γtot M r θ e μ a
    - (dCoord μ (fun r θ => g M a e r θ) r θ) * Γtot M r θ e ν b
    + (dCoord ν (fun r θ => g M a e r θ) r θ) * Γtot M r θ e μ b)
  =
  (fun e => ((f1 e + f2 e) + f3 e) + f4 e) := by
  -- No re-association here: choose (((f1+f2)+f3)+f4) to match how `+` nests.
  funext e
  simp only [f1, f2, f3, f4]  -- ✅ FIXED
```

---

## Progression of Fixes

### Attempt 1: JP's First Corrected Solution (Build: `build_jp_corrected_solution_oct30.txt`)
- **Status**: ❌ Failed with 25 errors
- **Issue**: Tactical error at line 1757 - type mismatch in sum splitting
- **Root cause**: Pattern structure didn't match expected type

### Attempt 2: JP's Heartbeat-Safe Solution (Build: `build_jp_final_fix_oct30.txt`)
- **Status**: ❌ Failed with 29 errors
- **Issue**: Deterministic timeout at lines 1768, 1771, 1773, 1779, 1785
- **Root cause**: Global AC-normalization on huge Christoffel expressions

### Attempt 3: Fix Forward Reference (Build: `build_sumidx_congr_moved_oct30.txt`)
- **Status**: ❌ Failed with 26 errors
- **Issue**: Line 1743 - `Unknown identifier 'sumIdx_congr'`
- **Fix**: Moved `sumIdx_congr` from line 1825 to line 1696
- **Result**: Forward reference fixed, but revealed new error at line 1774

### Attempt 4: Fix `rfl` Failure (Current - Build: `build_hpack_fix_oct30.txt`)
- **Status**: ⚙️ **BUILDING**
- **Issue**: Line 1774 - `rfl` failed because `set` definitions not unfolded
- **Fix**: Replace `rfl` with `simp only [f1, f2, f3, f4]`
- **Expected**: Should resolve line 1774 error and move forward

---

## Expected Outcome

**If successful**:
- Error count should drop from 26 to 25 or lower
- `payload_split_and_flip` lemma should compile past line 1774
- May reveal additional errors in later parts of the proof (lines 1775+)

**If still failing**:
- Extract new error message and diagnose
- Report to JP with exact goal state and error details
- May need additional tactical adjustments

---

## Files Modified

**Riemann.lean:1774**: Changed `rfl` → `simp only [f1, f2, f3, f4]`

---

## Build Monitoring

**Command**:
```bash
lake build Papers.P5_GeneralRelativity.GR.Riemann 2>&1 | tee Papers/P5_GeneralRelativity/GR/build_hpack_fix_oct30.txt
```

**Monitoring** (after 2 minutes):
```bash
tail -100 Papers/P5_GeneralRelativity/GR/build_hpack_fix_oct30.txt | grep -E "^error:|Built Papers|build failed|payload_split_and_flip" | tail -50
```

**Error count check**:
```bash
grep -c "^error:" Papers/P5_GeneralRelativity/GR/build_hpack_fix_oct30.txt 2>/dev/null
```

---

## Context: JP's Heartbeat-Safe Strategy

JP's proof strategy is designed to avoid all expensive operations:

1. **Step 1 (hflip_pt, hflip)**: Flip factors pointwise using `mul_comm` - local operations only
2. **Step 2 (hpack)**: Fix parenthesization to `(((f1+f2)+f3)+f4)` - just structural equality ← **WE ARE HERE**
3. **Step 3 (h1, h2, h3)**: Split using three small `sumIdx_add_distrib` applications - tiny goals
4. **Step 4 (calc chain)**: Assemble with small scalar associativity reshapes - no unfolding

The `hpack` step is critical because it ensures the term structure matches what the splitting lemmas expect.

---

**Prepared by**: Claude Code (Lean 4 Assistant)
**Date**: October 30, 2025
**Build**: In progress - `build_hpack_fix_oct30.txt`
**Status**: ⚙️ Fix applied, awaiting build verification
**Priority**: **HIGH** - Continuing implementation of JP's heartbeat-safe solution

---

## Related Documentation

- `DIAGNOSTIC_TIMEOUT_JP_FINAL_FIX_OCT30.md` - Timeout errors from first heartbeat-safe attempt
- `DIAGNOSTIC_TACTICAL_FIX_ATTEMPT_OCT30.md` - Type mismatch in JP's first corrected solution
- `SUCCESS_JP_CORRECTED_SOLUTION_OCT30.md` - Status before heartbeat-safe solution

---

**End of Report**
