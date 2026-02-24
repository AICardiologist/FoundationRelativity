# Implementation Status: JP's Splitter Solution (Partial)

**Date**: October 29, 2025
**Status**: ⚠️ **Partial Implementation - Needs Correction**

---

## Summary

Attempted to implement JP's solution for the 2 ΓΓ splitter errors but encountered implementation issues. The new `sumIdx_factor_const_from_sub_left` lemma was successfully added and relocated, but the proof application pattern causes recursion depth errors.

### Error Count Progression
- **Baseline** (calc block breakthrough): 21 errors
- **After implementation**: 25 errors (+4 errors)

---

## What Was Implemented

### 1. New Lemma Added (Lines 1614-1624)

Successfully added the `sumIdx_factor_const_from_sub_left` lemma after `mul_sumIdx`:

```lean
/-- Factor a left constant through a `sumIdx` of a difference. -/
lemma sumIdx_factor_const_from_sub_left (c : ℝ) (A B : Idx → ℝ) :
  sumIdx (fun k => c * A k - c * B k) = c * (sumIdx A - sumIdx B) := by
  classical
  calc
    sumIdx (fun k => c * A k - c * B k)
        = sumIdx (fun k => c * A k) - sumIdx (fun k => c * B k) := by
            simpa using sumIdx_map_sub (fun k => c * A k) (fun k => c * B k)
    _   = c * sumIdx A - c * sumIdx B := by
            simp [mul_sumIdx]
    _   = c * (sumIdx A - sumIdx B) := by ring
```

**Note**: `@[simp]` attribute was removed to avoid automatic simp loop.

### 2. B-Branch Fix Attempted (Lines 7506-7523)

Added packing helper and application:

```lean
have h_pack :
  sumIdx (fun ρ =>
    g M b b r θ * (Γtot M r θ ρ μ a * Γtot M r θ b ν ρ)
  - g M b b r θ * (Γtot M r θ ρ ν a * Γtot M r θ b μ ρ))
  =
  g M b b r θ *
    ( sumIdx (fun ρ => Γtot M r θ ρ μ a * Γtot M r θ b ν ρ)
    - sumIdx (fun ρ => Γtot M r θ ρ ν a * Γtot M r θ b μ ρ) ) := by
  simpa using
    sumIdx_factor_const_from_sub_left
      (g M b b r θ)
      (fun ρ => Γtot M r θ ρ μ a * Γtot M r θ b ν ρ)
      (fun ρ => Γtot M r θ ρ ν a * Γtot M r θ b μ ρ)

rw [h_pack]
```

### 3. A-Branch Fix Attempted (Lines 7770-7787)

Mirror of b-branch with a/b swapped.

---

## The Problem

### Issue: Maximum Recursion Depth

**Error at line 7517**:
```
error: Tactic `simp` failed with a nested error:
maximum recursion depth has been reached
```

**Root cause**: Using `simpa using sumIdx_factor_const_from_sub_left ...` causes recursion because:
1. `simpa` tries to simplify the goal
2. During simplification, it unfolds or applies the lemma's proof
3. The lemma's proof itself uses `simpa` and `simp`
4. This creates infinite recursion with other sumIdx lemmas

### Attempted Fixes

1. ✅ **Relocated lemma** to after `mul_sumIdx` (dependency ordering)
2. ✅ **Removed `@[simp]` attribute** (didn't help - recursion persists)
3. ❌ **Still failing** with `simpa using` approach

---

## Next Steps Required

### Option 1: Use `exact` Instead of `simpa using`

Change lines 7517-7521 from:
```lean
simpa using
  sumIdx_factor_const_from_sub_left
    (g M b b r θ)
    (fun ρ => Γtot M r θ ρ μ a * Γtot M r θ b ν ρ)
    (fun ρ => Γtot M r θ ρ ν a * Γtot M r θ b μ ρ)
```

To:
```lean
exact
  sumIdx_factor_const_from_sub_left
    (g M b b r θ)
    (fun ρ => Γtot M r θ ρ μ a * Γtot parameter M r θ b ν ρ)
    (fun ρ => Γtot M r θ ρ ν a * Γtot M r θ b μ ρ)
```

And repeat for a-branch at lines 7781-7785.

### Option 2: Simplify Lemma Proof

Modify the `sumIdx_factor_const_from_sub_left` lemma to avoid using `simpa/simp` in its proof, which might prevent recursion when the lemma is used.

### Option 3: Consult JP

The implementation may need a different approach than what was attempted. JP's original guidance may have specified a different application pattern.

---

## Files Modified

### Riemann.lean
- Lines 1614-1624: New `sumIdx_factor_const_from_sub_left` lemma
- Lines 7506-7523: B-branch packing attempt (FAILING)
- Lines 7770-7787: A-branch packing attempt (FAILING)

### Build Logs
- `build_jp_solution_relocated_oct29.txt`: After lemma relocation (25 errors)
- `build_jp_solution_no_simp_oct29.txt`: After removing @[simp] (25 errors)

---

## Current Errors (25 total)

### New Errors Created by Implementation
1. Line 7517: Maximum recursion depth in b-branch h_pack
2. Line 7781: Maximum recursion depth in a-branch h_pack
3. Line 7248: Unsolved goals (cascading from 7517)
4. Line 7550: Unsolved goals (cascading from 7781)

### Pre-existing Errors (21 from baseline)
- Still present and unchanged

---

## Recommendations

1. **Immediate**: Try changing `simpa using` to `exact` at lines 7517 and 7781
2. **If that fails**: Remove the added fixes and revert to baseline, then consult JP on correct application pattern
3. **Long-term**: May need to understand the exact proof strategy JP intended

---

**Prepared by**: Claude Code
**Session date**: October 29, 2025
**Status**: Implementation incomplete - recursion depth blocker

**Key Finding**: The `sumIdx_factor_const_from_sub_left` lemma works correctly in isolation, but using `simpa using` to apply it creates recursion with other simp lemmas. Need to use direct application (`exact`) or different proof strategy.
