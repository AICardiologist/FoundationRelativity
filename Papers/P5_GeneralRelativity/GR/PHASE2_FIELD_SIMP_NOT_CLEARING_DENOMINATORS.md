# Phase 2 Component Lemmas - field_simp Not Clearing Denominators

**Date:** October 5, 2025
**Context:** Phase 2 Component Lemmas Implementation (Following Junior Professor's Guidance)
**Status:** BLOCKED - `field_simp` not clearing denominators despite correct hypotheses

---

## Executive Summary

Following Junior Professor's tactical fix from earlier today, I implemented the `hsub_nz` pattern across all 6 Schwarzschild Riemann component lemmas. However, `field_simp [hr_nz, hsub_nz, pow_two, sq]` is **not clearing denominators** as expected. The reciprocal terms `(r - M*2)⁻¹` remain in the goal, causing `ring` to fail.

**Current Status:** 14 errors with `lake build` (same as baseline c173658)
- 3 pre-existing infrastructure errors
- 5 component lemma errors (lines 4914, 4940, 4967, 4990, 5013) ← **NEW BLOCKING ISSUE**
- 4 diagonal Ricci case errors (unchanged)
- 2 additional errors

---

## What Junior Professor Recommended (October 5, 2025)

### The Fix That Should Work

**Junior Professor's Analysis:**
> "The issue is that `field_simp` wasn't clearing denominators because it didn't know that `r - M*2 ≠ 0`. After expanding `f M r = 1 - 2*M/r` to `1 - 2*M*r⁻¹`, the goal contains `(r - M*2)⁻¹`. Without knowing `r - M*2 ≠ 0`, `field_simp` cannot clear those denominators."

**Recommended Code:**
```lean
-- Prove that (r - 2M) is nonzero in the exterior
have hsub_nz : r - M * 2 ≠ 0 := by
  have hpos : 0 < r - 2 * M := sub_pos.mpr hr_ex
  simpa [mul_comm] using ne_of_gt hpos

-- Pass hsub_nz to field_simp
field_simp [hr_nz, hsub_nz, pow_two, sq]
ring
```

---

## What I Implemented

### Helper Lemma (lines 4907-4908)
```lean
lemma sub_twoM_ne_zero_of_exterior (M r : ℝ) (hr_ex : 2 * M < r) : r - M * 2 ≠ 0 := by
  linarith
```

### Pattern Applied to All 6 Component Lemmas

**Example (R_trtr, lines 4912-4936):**
```lean
lemma Riemann_trtr_eq (M r θ : ℝ) (hM : 0 < M) (hr_ex : 2 * M < r) :
    Riemann M r θ Idx.t Idx.r Idx.t Idx.r = -2 * M / r ^ 3 := by
  classical
  have hr_nz : r ≠ 0 := r_ne_zero_of_exterior M r hM hr_ex
  have hf_nz : f M r ≠ 0 := ne_of_gt (f_pos_of_hr M r hM hr_ex)
  have hsub_nz := sub_twoM_ne_zero_of_exterior M r hr_ex  -- ✅ ADDED

  [structural expansion steps...]

  simp [f, div_eq_mul_inv]
  field_simp [hr_nz, hsub_nz, pow_two, sq]  -- ✅ ADDED hsub_nz, pow_two, sq
  ring
```

**All 6 lemmas updated:**
1. ✅ R_trtr (lines 4912-4936)
2. ✅ R_tθtθ (lines 4938-4962)
3. ✅ R_tφtφ (lines 4964-4985)
4. ✅ R_rθrθ (lines 4987-5008)
5. ✅ R_rφrφ (lines 5010-5031)
6. ✅ R_θφθφ (lines 5033-5066)

---

## The Problem: field_simp Not Clearing Denominators

### R_trtr Error (line 4914)

**Goal after `field_simp [hr_nz, hsub_nz, pow_two, sq]`:**
```lean
M r θ : ℝ
hM : 0 < M
hr_ex : 2 * M < r
hr_nz : r ≠ 0
hf_nz : f M r ≠ 0
hsub_nz : r - M * 2 ≠ 0                                    ← WE HAVE THIS!
hder_tr : deriv (fun s => Γ_t_tr M s) r = -(2 * M) * (r * f M r + M) / (r ^ 4 * f M r ^ 2)
hder_rr : deriv (fun s => Γ_r_rr M s) r = 2 * M * (r * f M r + M) / (r ^ 4 * f M r ^ 2)
⊢ r * (r - M * 2)⁻¹ * 2 - M * (r - M * 2)⁻¹ * 4 = 2      ← DENOMINATORS NOT CLEARED!
```

**Expected:** `field_simp` should multiply through by `(r - M*2)`, clearing denominators:
```
⊢ r * 2 - M * 4 = 2 * (r - M * 2)
⊢ 2r - 4M = 2r - 4M  ✓ (trivial for ring)
```

**Actual:** Denominators remain, `ring` cannot solve.

---

### R_tθtθ Error (line 4940)

**Goal after `field_simp [hr_nz, hsub_nz, pow_two, sq]`:**
```lean
M r θ : ℝ
hM : 0 < M
hr_ex : 2 * M < r
hr_nz : r ≠ 0
hf_nz : f M r ≠ 0
hsub_nz : r - M * 2 ≠ 0                                    ← WE HAVE THIS!
⊢ -(r * M ^ 2 * (r - M * 2)⁻¹ * 4) + r ^ 2 * M * (r - M * 2)⁻¹ + M ^ 3 * (r - M * 2)⁻¹ * 4
  = r * M - M ^ 2 * 2                                      ← DENOMINATORS NOT CLEARED!
```

**Expected:** `field_simp` should clear `(r - M*2)⁻¹`, leaving a polynomial equation for `ring`.

**Actual:** Same issue - denominators remain.

---

### All 5 Component Lemma Errors Follow Same Pattern

1. **R_trtr (line 4914):** `⊢ r * (r - M * 2)⁻¹ * 2 - M * (r - M * 2)⁻¹ * 4 = 2`
2. **R_tθtθ (line 4940):** `⊢ -(r*M²*(r-M*2)⁻¹*4) + r²*M*(r-M*2)⁻¹ + M³*(r-M*2)⁻¹*4 = r*M - M²*2`
3. **R_tφtφ (line 4967):** Similar pattern with `sin²θ` factor
4. **R_rθrθ (line 4990):** Similar pattern
5. **R_rφrφ (line 5013):** Similar pattern with `sin²θ` factor

**Common thread:** Despite `hsub_nz : r - M * 2 ≠ 0` being in context and passed to `field_simp`, the `(r - M * 2)⁻¹` terms are not cleared.

---

## What I've Tried (All Failed)

### Attempt 1: Original Junior Professor's Code
```lean
have hsub_nz : r - M * 2 ≠ 0 := by
  have hpos : 0 < r - 2 * M := sub_pos.mpr hr_ex
  simpa [mul_comm] using ne_of_gt hpos
field_simp [hr_nz, hsub_nz, pow_two, sq]
ring
```
**Result:** `hsub_nz` compiles, but `field_simp` still doesn't clear denominators.

---

### Attempt 2: Simplified with `linarith`
```lean
lemma sub_twoM_ne_zero_of_exterior (M r : ℝ) (hr_ex : 2 * M < r) : r - M * 2 ≠ 0 := by
  linarith

have hsub_nz := sub_twoM_ne_zero_of_exterior M r hr_ex
field_simp [hr_nz, hsub_nz, pow_two, sq]
ring
```
**Result:** Same - denominators not cleared.

---

### Attempt 3: Including `hf_nz` in `field_simp`
```lean
field_simp [hr_nz, hf_nz, hsub_nz, pow_two, sq]
ring
```
**Result:** Same - denominators not cleared.

---

### Attempt 4: Without `hf_nz`
```lean
field_simp [hr_nz, hsub_nz, pow_two, sq]
ring
```
**Result:** Same - denominators not cleared.

---

## Root Cause Analysis

### Why is `field_simp` Not Working?

**Hypothesis 1: Pattern Mismatch**
- `hsub_nz` proves `r - M * 2 ≠ 0`
- Goal contains `(r - M * 2)⁻¹`
- Lean's `ring` normalizes `2*M` to `M*2` during simplification
- Could `field_simp` be looking for `r - 2*M ≠ 0` instead?

**Evidence Against:** Junior Professor specifically used `r - M*2` in the fix, suggesting this should work.

---

**Hypothesis 2: Simp Order Issue**
- `simp [f, div_eq_mul_inv]` runs before `field_simp`
- This expands `f M r = 1 - 2*M/r` into `1 - 2*M*r⁻¹`
- The subsequent algebra may create terms that `field_simp` doesn't recognize

**Evidence For:** The goal shows `(r - M*2)⁻¹`, which should match `hsub_nz`, but field_simp isn't acting on it.

---

**Hypothesis 3: field_simp Needs Explicit Discharge**
- Perhaps `field_simp` in Lean 4 requires the nonzero proof to be stated differently?
- Or needs additional lemmas about reciprocals?

**Evidence Unknown:** This is a Lean 4 tactic behavior question.

---

## Comparison with Baseline

**Baseline (commit c173658):** 9 errors with `lake build`
- 3 infrastructure errors
- 4 diagonal Ricci case errors (these use the component lemmas, so they're blocked)
- 2 other errors

**Current State:** 14 errors
- Same 3 infrastructure errors
- 5 new component lemma errors ← **BLOCKING**
- Same 4 diagonal Ricci case errors (downstream from component lemmas)
- Same 2 other errors

**Regression:** +5 errors from attempting component lemma implementation.

---

## Questions for Tactical Expert

### Q1: Is there a different tactic to clear denominators?

`field_simp` should work according to Junior Professor, but it doesn't. Alternatives to try:
- `field_simp!` (aggressive version)?
- `norm_num` before `ring`?
- Manual `rw` with reciprocal lemmas?
- `polyrith` (if available)?

### Q2: Should the proof structure change?

Instead of:
```lean
simp [f, div_eq_mul_inv]
field_simp [hr_nz, hsub_nz, pow_two, sq]
ring
```

Should we use:
```lean
-- Keep f symbolic longer?
calc [step-by-step calculation with explicit rewrites]
```

### Q3: Is there a missing import or lemma?

Does `field_simp` need additional imports to handle `(r - M*2)⁻¹` properly in Lean 4?

### Q4: Working Example Request

Could you provide a **complete, compilable proof** of just R_trtr or R_tθtθ showing exactly how to close this goal? Even if it uses tactics or approaches I haven't tried, a working example would clarify the correct path forward.

---

## Strategic Decision Point

### Continue with Junior Professor?

**Pros:**
- Already engaged with this specific tactical issue
- Provided the `hsub_nz` fix (though it didn't work as expected)
- Understands the proof structure we're attempting

**Cons:**
- The fix didn't work - may need a different tactical approach
- Cannot test code - relies on my implementation reports

---

### Escalate to Senior Professor?

**Pros:**
- May suggest a fundamentally different proof strategy
- Could identify if component lemma approach is flawed for this use case
- Broader strategic view of how to structure the Ricci proof

**Cons:**
- Not up to date on recent tactical details
- Would need extensive context about what we've tried
- May not have tactical-level debugging insights Junior Prof has

---

## Recommendation

**Consult Junior Professor first** with this specific question:

> "I implemented your `hsub_nz` fix exactly as recommended, but `field_simp [hr_nz, hsub_nz, pow_two, sq]` is not clearing the `(r - M*2)⁻¹` denominators. The goal still contains reciprocal terms after `field_simp` runs.
>
> For example, R_trtr goal after `field_simp`:
> `⊢ r * (r - M * 2)⁻¹ * 2 - M * (r - M * 2)⁻¹ * 4 = 2`
>
> We have `hsub_nz : r - M * 2 ≠ 0` in context. Why isn't `field_simp` clearing these denominators? Is there a different tactic or proof structure needed?"

**If Junior Professor cannot resolve:** Then escalate to Senior Professor with full context:
- Summary of component lemma approach
- Junior Professor's tactical guidance
- The specific `field_simp` blocking issue
- Request for alternative proof strategy

---

## Files Modified

**`/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean`**
- Added helper: `sub_twoM_ne_zero_of_exterior` (lines 4907-4908)
- Updated all 6 component lemmas with `hsub_nz` pattern (lines 4912-5066)

**Build Status:** 14 errors (regression from baseline 9)

---

## Next Steps

1. **Immediate:** Consult Junior Professor about why `field_simp` isn't clearing denominators
2. **If unresolved:** Escalate to Senior Professor for alternative proof strategy
3. **If still blocked:** Consider reverting to baseline c173658 and attempting a different approach to Phase 2

---

**Generated:** October 5, 2025
**Author:** Claude Code
**Purpose:** Detailed technical report on `field_simp` blocking issue for expert consultation
**Priority:** HIGH - All 6 component lemmas blocked by same tactical issue
