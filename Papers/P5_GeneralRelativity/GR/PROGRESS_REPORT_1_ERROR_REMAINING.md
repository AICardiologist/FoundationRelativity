# Progress Report - 1 Error Remaining After Applying Finishers

**Date**: October 7, 2025
**Previous**: 9 errors (after initial finisher application)
**Current**: 1 error
**Improvement**: 89% reduction ✅

---

## Summary

Successfully applied the Junior Professor's helper lemmas and finisher patterns, reducing errors from 9 to 1. All finishers now work correctly except for one lemma (Fix 4: R^φ_{θφθ}) which has an algebra issue unrelated to the `f M r` normalization pattern.

---

## All Fixes Applied ✅

### Helper Lemmas (lines 2047-2076)

1. **Mr_f_collapse** (lines 2047-2051) ✅
   ```lean
   lemma Mr_f_collapse (M r : ℝ) (hr : r ≠ 0) :
     M * r * f M r = M * r - 2 * M ^ 2 := by
     unfold f
     field_simp [hr]
   ```
   Fixed: Removed extra `ring` that caused "No goals to be solved"

2. **Mr_f_linearize** (lines 2053-2062) ✅
   ```lean
   lemma Mr_f_linearize (M r k : ℝ) (hr : r ≠ 0) :
     -(M * r * f M r * k) = -(M * r * k) + M ^ 2 * (2 * k) := by
     have hcollapse : M * r * f M r = M * r - 2 * M ^ 2 := Mr_f_collapse M r hr
     calc
       -(M * r * f M r * k)
           = -((M * r - 2 * M ^ 2) * k) := by simpa [hcollapse]
       _   = -(M * r * k) + (2 * M ^ 2) * k := by ring
       _   = -(M * r * k) + M ^ 2 * (2 * k) := by ring
   ```
   Status: Already robust per your guidance

3. **Mr_f_linearize_sym** (lines 2064-2068) ✅
   ```lean
   lemma Mr_f_linearize_sym (M r k : ℝ) (hr : r ≠ 0) :
     -(r * f M r * M * k) = -(M * r * k) + M ^ 2 * (2 * k) := by
     have h := Mr_f_linearize M r k hr
     simpa [mul_comm, mul_left_comm, mul_assoc] using h
   ```
   Status: Added as recommended

4. **collapse_r_sub_2M** (lines 2072-2076) ✅
   ```lean
   lemma collapse_r_sub_2M (M r k : ℝ) (hsub : r - 2 * M ≠ 0) :
     ((-(M * r) + 2 * M ^ 2) * k) * (r - 2 * M)⁻¹ = -(M * k) := by
     have hsub' : r - M * 2 ≠ 0 := by convert hsub using 2; ring
     field_simp [hsub']
     ring
   ```
   Fixed: Added `hsub'` conversion because `field_simp` produces `(r - M*2)` not `(r - 2*M)`

### Finisher Applications

#### Fix 1: RiemannUp_r_trt_ext (lines 2080-2114)
**Goal**: `= -(2*M) * f M r / r^3`

Already working, no finisher needed. Goal statement contains `f M r`.

#### Fix 2: RiemannUp_t_θtθ_ext (lines 2139-2163) ✅
**Goal**: `= -M / r`

Applied finisher:
```lean
field_simp [hr, hf, pow_two]
ring
have := Mr_f_linearize M r 1 hr
simp at this
exact this.symm
```

**Unsolved goal after `ring`**:
```
⊢ -(M * r) + M ^ 2 * 2 = -(M * r * f M r)
```

**Fix**: Use `Mr_f_linearize M r 1 hr` backwards (with `simp` to remove `* 1`, then `.symm`)

#### Fix 3: RiemannUp_r_θrθ_ext (lines 2166-2202) ✅
**Goal**: `= -M / r`

Applied finisher:
```lean
field_simp [hr, hf, pow_two]
ring
have h1 := Mr_f_linearize_sym M r 2 hr
have h2 := Mr_f_linearize_sym M r 1 hr
simp at h1 h2
rw [h1, h2]
ring
```

**Unsolved goal after `ring`**:
```
⊢ -(r * f M r * M * 2) + (r * M - M ^ 2 * 2) = -(r * f M r * M)
```

**Fix**: Apply both `Mr_f_linearize_sym M r 2 hr` and `M r 1 hr` with `simp` to remove `* 1/2`

#### Fix 4: RiemannUp_φ_θφθ_ext (lines 2205-2227) ❌
**Goal**: `= (2*M) / r`

**Status**: UNSOLVED GOALS (the 1 remaining error)

Current proof ends with:
```lean
rw [shape]
simp only [deriv_Γ_φ_θφ_at θ h_sin_nz, Γ_φ_rφ, Γ_r_θθ, Γ_φ_θφ, div_eq_mul_inv]
field_simp [hr, h_sin_nz, pow_two]
ring
```

**Unsolved goal after `ring`** (line 2207):
```
M r θ : ℝ
h_ext : Exterior M r θ
h_sin_nz : sin θ ≠ 0
hr : r ≠ 0
shape : RiemannUp M r θ φ Idx.θ φ Idx.θ =
    -deriv (fun t => Γ_φ_θφ t) θ + Γ_φ_rφ r * Γ_r_θθ M r - Γ_φ_θφ θ * Γ_φ_θφ θ
⊢ -(deriv (fun t => cos t * (sin t)⁻¹) θ * r * sin θ ^ 2)
  + (-(r * sin θ ^ 2) - r * cos θ ^ 2)
  + M * sin θ ^ 2 * 2
  = M * sin θ ^ 2 * 2
```

**Analysis**:
- LHS should simplify to RHS algebraically
- The derivative `deriv(cot θ) = deriv(cos θ / sin θ) = -csc² θ = -1/(sin θ)²`
- So: `-deriv(cot) * r * sin² θ = -(-1/sin² θ) * r * sin² θ = r`
- Then: `r + (-(r·sin²θ) - r·cos²θ) + 2M·sin²θ = r - r + 2M·sin²θ = 2M·sin²θ` ✓

**Issue**: The lemma `deriv_Γ_φ_θφ_at` might not be providing the derivative in the form Lean needs, or the simplification isn't happening automatically.

**Note from Junior Professor**: You marked Fix 4 as "already correct per user's guidance", but it has unsolved goals.

#### Fix 5: RiemannUp_t_φtφ_ext (lines 2230-2260) ✅
**Goal**: `= -(M * Real.sin θ ^ 2) / r`

Applied finisher (replaced `hcombine`/`hcollapse` pattern):
```lean
field_simp [hr, hf, pow_two]
ring
have := Mr_f_linearize M r 1 hr
simp at this
have : -(M * r * sin θ ^ 2) + M ^ 2 * sin θ ^ 2 * 2
     = -(M * r * sin θ ^ 2 * f M r) := by
  have h := this
  calc -(M * r * sin θ ^ 2) + M ^ 2 * sin θ ^ 2 * 2
      = sin θ ^ 2 * (-(M * r) + M ^ 2 * 2) := by ring
  _   = sin θ ^ 2 * (-(M * r * f M r)) := by rw [← h]
  _   = -(M * r * sin θ ^ 2 * f M r) := by ring
exact this
```

**Why `hcombine`/`hcollapse` didn't work**: After `field_simp [hr, hf, pow_two]`, all the `(r-2*M)⁻¹` terms were cleared, so the pattern matching failed. Had to prove the equality directly using `Mr_f_linearize` with a `calc` chain.

#### Fix 6: RiemannUp_r_φrφ_ext (lines 2263-2305) ✅
**Goal**: `= -(M * Real.sin θ ^ 2) / r`

Applied finisher (replaced `hfold`/`hcombine` pattern):
```lean
field_simp [hr, hf, pow_two]
ring
have h1 := Mr_f_linearize_sym M r 2 hr
have h2 := Mr_f_linearize_sym M r 1 hr
simp at h1 h2
have : -(sin θ ^ 2 * r * f M r * M * 2)
     + (sin θ ^ 2 * r * M - sin θ ^ 2 * M ^ 2 * 2)
     = -(sin θ ^ 2 * r * f M r * M) := by
  have key : -(r * f M r * M * 2) + (r * M - M ^ 2 * 2)
           = -(r * f M r * M) := by
    linarith [h1, h2]
  calc -(sin θ ^ 2 * r * f M r * M * 2)
       + (sin θ ^ 2 * r * M - sin θ ^ 2 * M ^ 2 * 2)
      = sin θ ^ 2 * (-(r * f M r * M * 2) + (r * M - M ^ 2 * 2)) := by ring
  _   = sin θ ^ 2 * (-(r * f M r * M)) := by rw [key]
  _   = -(sin θ ^ 2 * r * f M r * M) := by ring
exact this
```

**Why the original pattern didn't work**: Same as Fix 5 - `field_simp` cleared all inverses, so had to factor out `sin θ ^ 2` and use `linarith [h1, h2]` to combine the linearize lemmas.

---

## Key Insight: The `field_simp` Issue

Your finisher patterns assumed that after `field_simp [hr, hf, pow_two]` and `ring`, there would still be `(r-2*M)⁻¹` terms in the goal that could be rewritten with `hcombine` and collapsed with `collapse_r_sub_2M`.

**What actually happened**:
- `field_simp [hr, hf, ...]` clears ALL denominators, including `(r-2*M)⁻¹`
- After `ring`, the goal has NO inverse terms left
- So `hcombine` (which expects to match inverse terms) fails with "Did not find an occurrence of the pattern"

**Solution**:
- For Fixes 5-6, I replaced the `hcombine`/`hcollapse`/`hfold` patterns with direct applications of `Mr_f_linearize` using `calc` chains and `linarith`
- This works because the goal (after clearing denominators) is just an algebraic equality about `f M r` terms

---

## Build Status

```bash
cd /Users/quantmann/FoundationRelativity
lake build Papers.P5_GeneralRelativity.GR.Riemann
```

**Result**: 1 error (down from 9)

```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:2207:57: unsolved goals
```

---

## Questions for Junior Professor

### Q1: Fix 4 (R^φ_{θφθ}) - Derivative Simplification

The unsolved goal in Fix 4 is:
```
⊢ -(deriv (fun t => cos t * (sin t)⁻¹) θ * r * sin θ ^ 2)
  + (-(r * sin θ ^ 2) - r * cos θ ^ 2)
  + M * sin θ ^ 2 * 2
  = M * sin θ ^ 2 * 2
```

This **should** simplify algebraically:
- `deriv(cot θ) = -csc² θ = -1/(sin θ)²`
- So LHS = `r - r(sin²θ + cos²θ) + 2M·sin²θ = 2M·sin²θ` = RHS ✓

But Lean isn't seeing this. The lemma uses:
```lean
simp only [deriv_Γ_φ_θφ_at θ h_sin_nz, Γ_φ_rφ, Γ_r_θθ, Γ_φ_θφ, div_eq_mul_inv]
```

**Question**: Is `deriv_Γ_φ_θφ_at` providing the derivative in the right form? Should I add a normalization lemma for the cotangent derivative, or is there a missing simplification step?

### Q2: field_simp Behavior

In Fixes 5-6, your finisher patterns expected `(r-2*M)⁻¹` terms to still be present after `field_simp [hr, hf, pow_two]` and `ring`, but `field_simp` eliminated all denominators.

**Question**: Was the intent for `field_simp` to preserve the inverse terms, or should the finishers work differently when denominators are cleared?

### Q3: Fix 4 Classification

You said Fix 4 was "already correct per user's guidance" in your original instructions, but it has unsolved goals.

**Question**: Was Fix 4 supposed to need a finisher, or is this a different issue (e.g., missing derivative lemma)?

---

## Files Modified This Session

- `GR/Riemann.lean`:
  - Lines 2047-2076: Helper lemmas (Mr_f_collapse, Mr_f_linearize, Mr_f_linearize_sym, collapse_r_sub_2M)
  - Lines 2161-2163: Fix 2 finisher
  - Lines 2198-2202: Fix 3 finisher
  - Lines 2252-2260: Fix 5 finisher (replaced hcombine/hcollapse)
  - Lines 2293-2305: Fix 6 finisher (replaced hfold/hcombine)

---

## Next Steps

**Option A**: Fix the derivative issue in Fix 4
- Add a lemma showing `deriv (fun t => cos t * (sin t)⁻¹) θ = -(sin θ)⁻²`
- Or find the right `simp` lemma to normalize the derivative

**Option B**: Investigate if Fix 4's algebra is actually correct
- Check if `deriv_Γ_φ_θφ_at` is computing the right value
- Verify the Γ symbol definitions expand correctly

**Option C**: Ask for guidance on Fix 4's proof strategy
- Perhaps Fix 4 needs a different approach than the other fixes

---

**Status**: 🟡 8/9 fixes complete, 1 error remaining (Fix 4 derivative issue)
