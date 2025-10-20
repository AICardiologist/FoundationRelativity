# Quick Followup: Almost There, Mysterious `case h` Persists
## Date: October 19, 2025
## Status: Fixes applied, 99% working, one remaining issue

---

## ✅ What I've Applied

All three of your fixes have been implemented exactly as specified:

### 1. `dΓ₁_r` with direction-mismatch (lines 4339-4383)
```lean
have dΓ₁_r : ... := by
  classical
  have hΣ : ... := by
    refine dCoord_sumIdx Idx.r ...
      (by intro ρ; left; exact (...).mul (...))  -- r-diff
      (by intro ρ; right; simp)                   -- μ ≠ θ mismatch ✅
  have hprod : ... := by
    funext ρ
    simpa using dCoord_mul_of_diff Idx.r ...
      (Or.inl (...))                              -- r-diff
      (Or.inl (...))                              -- r-diff
      (Or.inr (by simp))                          -- μ ≠ θ mismatch ✅
      (Or.inr (by simp))                          -- μ ≠ θ mismatch ✅
  simpa [Γ₁, hprod] using hΣ
```

### 2. `dΓ₁_θ` with direction-mismatch (lines 4386-4429)
Mirror of above with r/θ swapped - compiles structurally ✅

### 3. `cancel_r` and `cancel_θ` (lines 4478-4498)
Changed from `simpa using (...)` to `exact (...)` ✅

---

## ⚠️ Remaining Issue: `case h` Still Appears

**Error**:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:4344:79: unsolved goals
case h
M r θ : ℝ
h_ext : Exterior M r θ
h_θ : sin θ ≠ 0
a b : Idx
compat_r_a_e : ...
compat_θ_a_e : ...
H₁ : ...
H₂ : ...
f1 : Idx → ℝ := ...
f2 : Idx → ℝ := ...
f3 : Idx → ℝ := ...
f4 : Idx → ℝ := ...
f5 : Idx → ℝ := ...
f6 : Idx → ℝ := ...
goal_shape : ...
branch_r_merge : ...
branch_θ_merge : ...
regroup_no2 : ...
```

**Observations**:
1. Line 4344:79 is the end of the `dΓ₁_r` type signature (the `:= by`)
2. The `case h` context shows all the definitions from earlier in `regroup_left_sum_to_RiemannUp` (f1...f6, H₁, H₂, branch_r_merge, etc.)
3. This suggests something from the outer proof context is leaking into the `final` block
4. **Progress**: The sorry count went from 21 → 19, meaning the two `dΓ₁` proofs are being parsed (just not closing)

**What's puzzling**:
- The direction-mismatch approach using `Or.inr (by simp)` should have eliminated the extra obligations
- The structure exactly matches your drop-in code
- `hΣ` and `hprod` are defined correctly and their types look right
- The `simpa [Γ₁, hprod] using hΣ` should close the goal

**Hypothesis**:
Could the nested `classical` (line 4345 inside `dΓ₁_r`, while there's already one at line 4316 for the outer `final` proof) be creating an extra case?  Or is there some scoping issue where the `have` statements inside `final` are somehow interacting with the outer context?

---

## 🔍 Request for Guidance

The code is 99% there - just this `case h` blocking. A few possibilities:

1. **Tactic variant**: Should I use something other than `simpa [...] using hΣ`? Maybe `rw [← hΣ]; simp [Γ₁, hprod]`?

2. **Scope issue**: Do I need to explicitly close some tactic block or add a `done` somewhere?

3. **Missing import or instance**: Could there be a missing typeclass instance that's causing `simp` to leave an extra goal?

4. **Debugging approach**: Is there a way to see exactly what goal `simpa` is leaving unsolved? The error just shows `case h` with no actual goal statement.

---

## 📊 Current State

**Sorries**: 19 (same as before - the two `dΓ₁` sorries are now actual proof attempts)
**Compiles**: No (unsolved goals)
**Code structure**: ✅ 100% matches your specifications

**Files**: All changes in `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean`
- Lines 4339-4383: `dΓ₁_r` with your direction-mismatch fix
- Lines 4386-4429: `dΓ₁_θ` with your direction-mismatch fix
- Line 4487: `cancel_r` changed to `exact`
- Line 4498: `cancel_θ` changed to `exact`

Would appreciate any insight on what might cause this `case h` to persist despite the mismatch obligations being handled!

---

**Prepared by**: Claude Code
**Date**: October 19, 2025
**Status**: Awaiting guidance on `case h` resolution
