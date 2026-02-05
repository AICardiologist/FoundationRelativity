# Patch Compilation Failure Report
**Date**: October 7, 2025
**Status**: ❌ Patches DO NOT compile
**Total Errors**: 12 tactical errors + 3 sorries from earlier work

---

## Executive Summary

The user-provided patches for completing Stage 2 (diagonal Ricci cases) **do not compile successfully**. All 9 component lemmas and the derivative helper `deriv_Γ_r_tt_at` have tactical errors that prevent compilation.

**Key Finding**: The patches appear to be theoretical/skeletal implementations that need tactical refinement. The mathematical values are likely correct, but the Lean 4 proofs require additional tactical work to close.

---

## Error Category Breakdown

### 1. Derivative Helper Lemma: `deriv_Γ_r_tt_at` (Line 984-1018)

**Errors**: 5 tactical failures

#### Error 1.1 (Line 999): `simpa` goal mismatch
```
this : deriv (fun y => y⁻¹ * y⁻¹) r = (-r + -r) / (r * r * (r * r))
⊢ deriv (fun s => s⁻¹ * s⁻¹) r = -(2 * r) / r ^ 4
```

**Problem**: The `deriv_inv_general` lemma produces `(s^2)^(-1)` expanded as `y⁻¹ * y⁻¹`, but the goal expects `(s^2)⁻¹`. The simplification pattern doesn't match.

**Root cause**: API mismatch - `deriv_inv_general` returns a different form than expected.

#### Error 1.2 (Line 1004): Type mismatch in `deriv_mul`
```
DifferentiableAt.inv hd_s2
has type
  r ^ 2 ≠ 0 → DifferentiableAt ℝ (fun s => s ^ 2)⁻¹ r
but is expected to have type
  DifferentiableAt ℝ ?m.351 r
```

**Problem**: `hd_s2.inv` requires a proof that `r^2 ≠ 0`, but this wasn't provided as an argument.

**Fix needed**: Supply the nonzero proof explicitly:
```lean
have hr2_nz : r^2 ≠ 0 := by simpa [pow_two] using pow_ne_zero 2 hr
have := deriv_mul ((contDiffAt_f M r hr).differentiableAt le_top) (hd_s2.inv hr2_nz)
```

#### Error 1.3 (Line 1010): Goal mismatch after simp
```
⊢ deriv (fun s => M * f M s * (s ^ 2)⁻¹) r = M * deriv (fun y => f M y * (y ^ 2)⁻¹) r
```

**Problem**: The `simp [Γ_r_tt, div_eq_mul_inv]` doesn't exactly match the required form. The left side has `M * f M s * (s^2)⁻¹` but the unfolding produced a different association.

**Fix needed**: Use `rw [Γ_r_tt]` then `simp only [div_eq_mul_inv, mul_assoc]` for precise control.

#### Error 1.4 (Line 1013): Type mismatch with `hprod`
```
hprod
 has type
  deriv (...) = 2 * M / r ^ 2 * (r ^ 2)⁻¹ + f M r * (-(2 * r) / r ^ 4)
but is expected to have type
  deriv (...) = 2 * M / r ^ 2 * (r ^ 2)⁻¹ + -(f M r * (2 * r / r ^ 4)) ∨ M = 0
```

**Problem**: The `simpa [sub_eq_add_neg]` is producing a disjunction `∨ M = 0` unexpectedly. This suggests `simpa` is applying too many lemmas.

**Fix needed**: Use `rw [hprod, sub_eq_add_neg]` then `congr 1; ring` to control the rewrite precisely.

#### Error 1.5 (Line 1015): No goals to be solved
```
No goals to be solved
```

**Problem**: The previous step (`simpa`) closed the goal prematurely, so the next `field_simp; ring` has nothing to work on.

**Consequence**: This caused a cascade - once line 1013 failed, the rest of the calc chain broke.

---

### 2. Component Lemma: `RiemannUp_r_trt_ext` (Line 2006-2016)

**Error**: Unsolved goal after all tactics (Line 2011)

```lean
⊢ -(M ^ 2 * r * (-(M * 2) + r)⁻¹ * 2) + M ^ 3 * (-(M * 2) + r)⁻¹ * 4 +
      deriv (fun s => M * s⁻¹ ^ 2 - M ^ 2 * s⁻¹ ^ 3 * 2) r * r ^ 4 =
    -(M * r * 2) + M ^ 2 * 4
```

**Analysis**:
- The `field_simp [hr]; ring` at line 2011 left an unsolved algebraic goal
- The goal contains a derivative term that wasn't simplified: `deriv (fun s => M * s⁻¹ ^ 2 - M ^ 2 * s⁻¹ ^ 3 * 2) r`
- This derivative is the expanded form of `deriv Γ_r_tt`, but it wasn't substituted with `hder`

**Why it failed**:
1. The `hder` lemma states `deriv (fun s => Γ_r_tt M s) r = ...`
2. But after simp expansion, the goal has `deriv (fun s => M * s⁻¹ ^ 2 - M ^ 2 * s⁻¹ ^ 3 * 2) r`
3. These don't match syntactically, so `simp [hder]` doesn't apply

**Fix needed**:
```lean
-- After unfolding RiemannUp and simp steps, need to:
conv_lhs =>
  arg 2; arg 1  -- Navigate to the deriv term
  rw [show (fun s => M * s⁻¹ ^ 2 - M ^ 2 * s⁻¹ ^ 3 * 2) = (fun s => Γ_r_tt M s) from rfl]
simp [hder]
field_simp [hr]; ring
```

Or simplify before the derivative gets expanded.

---

### 3. Component Lemma: `RiemannUp_θ_tθt_ext` (Line 2018-2040)

**Errors**: 2 "No goals to be solved" (Lines 2035, 2045)

**Problem**: The proof has extra tactics after the goal was already closed by an earlier line.

**Likely cause**: The patch was written for a different Lean state, or was skeleton code that needs adjustment.

**Fix needed**: Remove the extra tactics or restructure the proof.

---

### 4. Component Lemma: `RiemannUp_φ_tφt_ext` (Line 2042-2050)

**Error**: Same as above - tactical structure mismatch.

---

### 5. Component Lemma: `RiemannUp_t_θtθ_ext` (Line 2052-2062)

**Error**: Unsolved algebraic goal (Line 2052)

```lean
⊢ -(M * r * (f M r)⁻¹) + M ^ 2 * (f M r)⁻¹ * 2 = -(M * r)
```

**Analysis**:
- Goal has `f M r` in denominators
- Need to expand `f M r = 1 - 2M/r` and simplify
- The `field_simp [hr]; ring` didn't expand `f`

**Fix needed**:
```lean
field_simp [hr, f]  -- Include f in the simp set
ring
```

Or:
```lean
simp only [f]
field_simp [hr]
ring
```

**Pattern**: This error repeats in multiple lemmas - they all need `f` expanded before `field_simp`.

---

### 6. Component Lemma: `RiemannUp_r_θrθ_ext` (Line 2064-2074)

**Error**: Unsolved algebraic goal (Line 2064)

```lean
⊢ r * M * (r - M * 2)⁻¹ + (-(M * 2) - M ^ 2 * (r - M * 2)⁻¹ * 2) = -M
```

**Same pattern**: `field_simp` didn't fully simplify the expression. Needs `f` expansion.

---

### 7. Component Lemma: `RiemannUp_φ_θφθ_ext` (Line 2077-2088)

**Error**: Unsolved goal with derivative (Line 2077)

```lean
⊢ -(deriv (fun t => cos t * (sin t)⁻¹) θ * r) - r * cos θ ^ 2 * (sin θ)⁻¹ ^ 2 + Γ_r_θθ M r = M * 2
```

**Problem**: The derivative `deriv (fun t => cos t * (sin t)⁻¹) θ` wasn't evaluated.

**Expected**: This should equal `deriv (Γ_θ_φφ) θ` which has a known lemma.

**Why it failed**: Pattern mismatch between the computed derivative and the lemma statement.

**Note**: The code references `deriv_Γ_θ_φφ_at` in the simp list, but Lean reports it's unused - meaning the pattern didn't match.

---

### 8. Component Lemma: `RiemannUp_t_φtφ_ext` (Line 2092-2101)

**Error**: Unsolved algebraic goal (Line 2092)

```lean
⊢ -(M * r * sin θ ^ 2 * (-(M * 2) + r)⁻¹) + M ^ 2 * sin θ ^ 2 * (-(M * 2) + r)⁻¹ * 2 = -(M * sin θ ^ 2)
```

**Same pattern as #5-6**: Missing `f` expansion.

---

### 9. Component Lemma: `RiemannUp_r_φrφ_ext` (Line 2103-2112)

**Error**: Unsolved algebraic goal (Line 2103)

```lean
⊢ sin θ ^ 2 * r * M * (r - M * 2)⁻¹ + (-(sin θ ^ 2 * M * 2) - sin θ ^ 2 * M ^ 2 * (r - M * 2)⁻¹ * 2) = -(sin θ ^ 2 * M)
```

**Same pattern**: Needs `f` expansion.

---

### 10. Component Lemma: `RiemannUp_θ_φθφ_ext` (Line 2114-2122)

**Error**: Unsolved algebraic goal (Line 2114)

```lean
⊢ sin θ * cos θ ^ 2 * r * (sin θ)⁻¹ + (sin θ ^ 2 * r - sin θ ^ 3 * r * (sin θ)⁻¹) +
      (sin θ ^ 3 * M * (sin θ)⁻¹ * 2 - cos θ ^ 2 * r) =
    sin θ ^ 2 * M * 2
```

**Problem**: Complex trigonometric simplification. Needs:
1. Simplify `sin θ * (sin θ)⁻¹ = 1`
2. Use `sin² θ + cos² θ = 1`
3. Then algebraic simplification

**Fix needed**:
```lean
field_simp [hθ]  -- where hθ : sin θ ≠ 0
-- Then use trig identities
have : sin θ ^ 2 + cos θ ^ 2 = 1 := sin_sq_add_cos_sq θ
ring_nf
-- Manual algebra may be needed
```

---

## Systematic Issues

### Issue A: Missing `f` expansion

**Affected lemmas**: 5, 6, 8, 9 (RiemannUp_t_θtθ_ext, RiemannUp_r_θrθ_ext, RiemannUp_t_φtφ_ext, RiemannUp_r_φrφ_ext)

**Pattern**: All use `field_simp [hr]; ring` but leave `f M r` unexpanded.

**Fix**: Change to `field_simp [hr, f]; ring` or `simp only [f]; field_simp [hr]; ring`

---

### Issue B: Derivative pattern mismatch

**Affected lemmas**: 1 (deriv_Γ_r_tt_at), 2 (RiemannUp_r_trt_ext), 7 (RiemannUp_φ_θφθ_ext)

**Pattern**: After simp expansion, derivative terms don't match the helper lemma statements.

**Fix**: Need to either:
1. Use `conv` tactics to navigate and rewrite the derivative term
2. Or simplify in a different order to avoid expanding the Christoffel symbols before applying derivative lemmas

---

### Issue C: Tactical structure mismatch

**Affected lemmas**: 3, 4 (RiemannUp_θ_tθt_ext, RiemannUp_φ_tφt_ext)

**Pattern**: "No goals to be solved" errors suggest the proof closed earlier than expected.

**Fix**: Remove extra tactics or restructure.

---

### Issue D: Complex trigonometric simplification

**Affected lemmas**: 10 (RiemannUp_θ_φθφ_ext)

**Pattern**: Mix of trig and algebraic terms that `ring` alone can't handle.

**Fix**: Add explicit trig identity lemmas before `ring`.

---

## Why These Patches Failed

### Hypothesis 1: Generated/Theoretical Code
The patches appear to be **skeleton implementations** with the correct mathematical values but incomplete tactical proofs. The user may have:
- Written these based on mathematical knowledge
- Generated them from a previous Lean version
- Had assistance from someone not familiar with the current codebase's API

**Evidence**:
- Systematic pattern of missing `f` expansion
- Derivative API mismatches
- Extra tactics that do nothing

### Hypothesis 2: Different Lean Environment
The patches may have been written for a different setup where:
- Simp lemmas behaved differently
- Christoffel symbol definitions expanded differently
- Derivative lemmas had different statements

**Evidence**:
- The structure is sound (unfold → simp → field_simp → ring)
- But specific tactical calls don't match the current environment

### Hypothesis 3: Incomplete Testing
The patches were likely **not tested** before being provided. Each lemma would need to be proven interactively to verify tactics work.

**Evidence**: All 9 component lemmas + helper fail - 0% success rate suggests no compilation testing.

---

## Recommended Fix Strategy

### Option A: Fix Systematically (Estimated 4-6 hours)

**For each lemma**:
1. Comment out the proof body, replace with `sorry`
2. Uncomment one tactic at a time
3. Check the goal after each step
4. Adjust tactics to match the actual goal state
5. Test build after each lemma completion

**Start with the simplest**: `RiemannUp_t_θtθ_ext` (just needs `f` expansion fix)

**Build up to complex**: `deriv_Γ_r_tt_at` (needs API investigation)

### Option B: Consult Junior Tactics Professor

**Request**: "Please help prove these component lemmas. I have the correct mathematical values but the tactical proofs fail."

**Provide**:
- List of 9 component lemmas with their target values
- This error report
- Request interactive proof development

**Timeline**: 1-2 sessions (2-4 hours)

### Option C: Hybrid Approach

**Step 1**: Fix the "easy" ones (Issue A - missing `f` expansion)
- Just add `f` to the `field_simp` argument
- Test: 4 lemmas should compile immediately

**Step 2**: Get help with derivative lemmas (Issue B)
- Consult Junior Professor for the 3 derivative-heavy lemmas

**Step 3**: Fix tactical structure (Issue C)
- Remove extra tactics from 2 lemmas

**Step 4**: Handle trigonometric case (Issue D)
- Last one, may need manual work

**Timeline**: Step 1 (30 min), Steps 2-4 (2-3 hours)

---

## Attempted Fixes This Session

### What We Tried

1. ✅ **Applied all 9 component lemma patches** (Lines 2006-2122)
2. ✅ **Applied derivative helper patch** (Lines 984-1018)
3. ✅ **Applied 3 cancellation lemmas** (Lines 2140-2187) - these actually compiled!
4. ✅ **Updated diagonal cases** (Lines 3624-3633) - had to use `convert` instead of direct `exact`
5. ✅ **Tested build** - Revealed 12 errors

### What Worked

- **Cancellation lemmas compile successfully!** (Lines 2140-2187)
  - `Ricci_tt_cancellation`
  - `Ricci_θθ_cancellation`
  - `Ricci_φφ_cancellation`

**Why these worked**: They just use simple substitution + algebraic simplification. No complex derivatives or pattern matching issues.

**Implication**: Once the component lemmas are fixed, the cancellation lemmas will work immediately.

### What Didn't Work

- Derivative helper `deriv_Γ_r_tt_at` - 5 errors
- All 9 component lemmas - tactical errors in each

---

## Current Repository State

**Commit**: Working off a87fa49 (last clean state with 6 sorries)

**Modified file**: `GR/Riemann.lean`

**Changes made**:
- Added lines 984-1018: `deriv_Γ_r_tt_at` (BROKEN)
- Added lines 2006-2122: 9 component lemmas (ALL BROKEN)
- Added lines 2140-2187: 3 cancellation lemmas (✅ WORKING)
- Modified lines 3624-3633: Diagonal case updates (attempt with `convert`)

**Build status**: ❌ 12 errors, does not compile

**Sorries**: 3 from earlier work (r.r case still incomplete) + unknown from broken lemmas

---

## Next Steps

### Immediate Action Required

**User decision needed**: Choose one of the three fix strategies above.

### If Proceeding with Fixes

**Quick win**: Try Option C Step 1 first
- Change `field_simp [hr]; ring` to `field_simp [hr, f]; ring` in 4 lemmas
- Test if this resolves Issue A
- If successful, reduces errors from 12 → ~8

### If Consulting Junior Professor

**Request template**:
> "I have 9 Riemann component lemmas with known mathematical values that need tactical proofs. The pattern is:
> ```lean
> lemma RiemannUp_X_YZW_ext ... : RiemannUp M r θ Idx.X Idx.Y Idx.Z Idx.W = <value> := by
>   classical
>   have hr : r ≠ 0 := Exterior.r_ne_zero h_ext
>   unfold RiemannUp
>   simp [dCoord, sumIdx_expand, Γtot, <relevant Christoffel symbols>]
>   field_simp [hr]; ring
> ```
>
> This pattern fails with algebraic goals that don't close. Can you help prove these interactively?"

---

## Lessons Learned

1. **Always test patches incrementally** - Don't apply all at once
2. **API differences matter** - Derivative lemmas have specific signatures
3. **Simp behavior is fragile** - Order of expansion matters
4. **Mathematical correctness ≠ tactical correctness** - Values may be right, but proofs need work

---

## Files Modified This Session

- `GR/Riemann.lean` - 138 lines added (984-1018, 2006-2122, 2140-2187, modifications at 3624-3633)
- `GR/PATCH_FAILURE_REPORT_OCT7_2025.md` (THIS FILE) - Error analysis

---

## Success Metrics

### Achieved ✅
- [x] Applied all user-provided patches
- [x] Identified all compilation errors (12 total)
- [x] Categorized errors into 4 systematic issues
- [x] Documented root causes
- [x] Proposed 3 fix strategies
- [x] Verified cancellation lemmas work

### Not Achieved ❌
- [ ] Get patches to compile
- [ ] Reduce sorries to 1 (r.r case)
- [ ] Complete Stage 2 of reconstruction

---

**Status**: Patches DO NOT compile - Detailed error analysis complete

**Recommendation**: Start with Option C (Hybrid) - Fix the 4 "missing `f`" lemmas first (30 min), then reassess.

---

**End of Patch Failure Report**

**Next Session**: Choose fix strategy and implement
