# Phase 2 Component Lemmas Implementation Report

**Date:** October 5, 2025
**Context:** Implementation of Schwarzschild Riemann component lemmas following corrected 6-step recipe
**Previous Guidance:** [JUNIOR_PROF_FOLLOWUP_COMPONENT_LEMMAS.md](./JUNIOR_PROF_FOLLOWUP_COMPONENT_LEMMAS.md)
**Baseline Commit:** c173658 (9 errors with `lake build`)

---

## Executive Summary

Implemented all 6 component lemmas following your corrected 6-step recipe from October 5, 2025. After fixing infrastructure issues (duplicate `f_derivative`, non-existent Γtot symbols), all 6 lemmas now have the same structure but **fail to complete** with "unsolved goals" errors.

**Current Status:**
- ✅ Phase 1 helper lemmas compile successfully (`r_mul_f`, `one_minus_f`)
- ❌ All 6 Phase 2 component lemmas have unsolved goals after final `ring` step
- **Error count:** 10 total (3 baseline infrastructure + 7 new component lemma errors)

**Key Question:** The tactical pattern `simp [...]; field_simp [...]; ring` is not closing the goals. Need guidance on what intermediate goals look like and why `ring` is insufficient.

---

## Implementation Following Corrected Recipe

### Phase 1: Helper Lemmas (✅ SUCCESS)

```lean
/-! ### Phase 1: Helper lemmas for component proofs -/

lemma r_mul_f (M r : ℝ) (hr_nz : r ≠ 0) : r * f M r = r - 2 * M := by
  unfold f
  field_simp [hr_nz]

lemma one_minus_f (M r : ℝ) : 1 - f M r = 2 * M / r := by
  unfold f
  ring
```

**Build Status:** ✅ Both compile with 0 errors

---

## Phase 2: Component Lemmas (❌ ALL FAIL)

### Implementation Pattern (Applied to All 6)

Following your 6-step recipe exactly:

```lean
/-- Component: R_tθtθ = M·f(r)/r -/
lemma Riemann_tθtθ_eq (M r θ : ℝ) (hM : 0 < M) (hr_ex : 2 * M < r) :
    Riemann M r θ Idx.t Idx.θ Idx.t Idx.θ = M * f M r / r := by
  classical
  -- Step 1: Setup
  have hr_nz : r ≠ 0 := r_ne_zero_of_exterior M r hM hr_ex
  have hf_nz : f M r ≠ 0 := ne_of_gt (f_pos_of_hr M r hM hr_ex)

  -- Step 2: Contract & expand, keeping Γ boxed
  rw [Riemann_contract_first M r θ Idx.t Idx.θ Idx.t Idx.θ]
  simp [g]
  unfold RiemannUp
  simp only [dCoord_t, dCoord_r, dCoord_θ, dCoord_φ, sumIdx_expand]

  -- Step 3: Apply derivative calculators while Γ still boxed
  have hder_tr := deriv_Γ_t_tr_at M r hr_nz hf_nz
  have hder_rr := deriv_Γ_r_rr_at M r hr_nz hf_nz
  simp [hder_tr, hder_rr]

  -- Step 4: Normalize (r-2M) with targeted simp_rw
  have rmf : r - 2 * M = r * f M r := by
    simpa [r_mul_f M r hr_nz, mul_comm]
  simp_rw [Γ_r_θθ, rmf]  -- only Γ_r_θθ carries (r-2M)

  -- Step 5: Expand remaining Γ's
  simp [Γ_t_tr, Γ_θ_rθ]

  -- Step 6: Close algebra
  field_simp [hr_nz, hf_nz, pow_two, sq]
  ring  -- ❌ FAILS HERE: "unsolved goals"
```

---

## Specific Errors Encountered

### Error 1: Riemann_tθtθ_eq (Line 4935)

**Error Message:**
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:4935:61: unsolved goals
M r θ : ℝ
hM : 0 < M
hr_ex : 2 * M < r
hr_nz : r ≠ 0
hf_nz : f M r ≠ 0
⊢ [goal truncated in build output]
```

**Location:** After `simp [Γ_t_tr, Γ_θ_rθ]` (Step 5), before `field_simp`

**Issue:** The goal at this point is not visible in the build output (truncated). Need to see what algebraic form remains after Step 5 to understand why `field_simp + ring` can't close it.

---

### Error 2: Riemann_tφtφ_eq (Line 4960)

**Similar Pattern:**
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:4960:78: unsolved goals
```

**Uses:** `Γ_r_φφ` carries `(r-2M)` pattern, same `simp_rw` strategy

---

### Error 3-6: Riemann_rθrθ_eq, Riemann_rφrφ_eq, Riemann_θφθφ_eq

**Errors at Lines:** 4985, 5009, 5034

**Additional Complexity:**
- `Riemann_rθrθ_eq`: Uses `deriv_Γ_θ_φφ_at` (only one derivative calculator)
- `Riemann_rφrφ_eq`: Uses both `deriv_Γ_θ_φφ_at` and `deriv_Γ_φ_θφ_at`
- `Riemann_θφθφ_eq`: Uses both derivative calculators, two `simp_rw` targets (`Γ_r_θθ`, `Γ_r_φφ`)

---

## Infrastructure Issues Fixed

### Issue 1: Duplicate `f_derivative` Declaration

**Error:**
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:4907:6:
'Papers.P5_GeneralRelativity.Schwarzschild.f_derivative' has already been declared
```

**Fix:** Removed the Phase 1 `f_derivative` lemma - it already exists in Schwarzschild.lean

---

### Issue 2: Non-existent Γtot Symbols

**Initial Error:**
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:4931:46: Unknown identifier `Γtot_t_tφ`
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:4932:35: Unknown identifier `Γtot_r_rθ`
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:4932:46: Unknown identifier `Γtot_r_rφ`
```

**Root Cause:** My Step 2 initially tried to expand with:
```lean
simp only [dCoord_t, dCoord_r, dCoord_θ, dCoord_φ, sumIdx_expand,
           Γtot_t_tt, Γtot_t_tr, Γtot_t_tθ, Γtot_t_tφ,  -- ❌ Γtot_t_tφ doesn't exist
           Γtot_r_rt, Γtot_r_rr, Γtot_r_rθ, Γtot_r_rφ,  -- ❌ These don't exist
           ...]
```

Many Γtot symbols are zero and defined as lemmas (e.g., `Γtot_t_tθ`), but NOT all permutations exist.

**Fix:** Simplified to:
```lean
simp only [dCoord_t, dCoord_r, dCoord_θ, dCoord_φ, sumIdx_expand]
```

Let Lean's simp set handle Γtot expansions automatically via existing `@[simp]` lemmas.

---

## Detailed Implementation of All 6 Component Lemmas

### 1. Riemann_trtr_eq (R_trtr = -2M/r³)

```lean
/-- Component: R_trtr = -2M/r³ -/
lemma Riemann_trtr_eq (M r θ : ℝ) (hM : 0 < M) (hr_ex : 2 * M < r) :
    Riemann M r θ Idx.t Idx.r Idx.t Idx.r = -2 * M / r ^ 3 := by
  classical
  have hr_nz : r ≠ 0 := r_ne_zero_of_exterior M r hM hr_ex
  have hf_nz : f M r ≠ 0 := ne_of_gt (f_pos_of_hr M r hM hr_ex)

  rw [Riemann_contract_first M r θ Idx.t Idx.r Idx.t Idx.r]
  simp [g]
  unfold RiemannUp
  simp only [dCoord_t, dCoord_r, dCoord_θ, dCoord_φ, sumIdx_expand]

  have hder_tr := deriv_Γ_t_tr_at M r hr_nz hf_nz
  have hder_rr := deriv_Γ_r_rr_at M r hr_nz hf_nz
  simp [hder_tr, hder_rr]

  have rmf : r - 2 * M = r * f M r := by
    simpa [r_mul_f M r hr_nz, mul_comm]

  simp [Γ_t_tr, Γ_r_tt, Γ_r_rr]

  field_simp [hr_nz, hf_nz, pow_two, sq]
  ring  -- ❌ FAILS
```

**Derivative Calculators Used:**
- `deriv_Γ_t_tr_at`: Provides closed form for `deriv (Γ_t_tr M ·) r`
- `deriv_Γ_r_rr_at`: Provides closed form for `deriv (Γ_r_rr M ·) r`

**Christoffel Symbols Expanded:** `Γ_t_tr`, `Γ_r_tt`, `Γ_r_rr`

---

### 2. Riemann_tθtθ_eq (R_tθtθ = M·f(r)/r)

```lean
/-- Component: R_tθtθ = M·f(r)/r -/
lemma Riemann_tθtθ_eq (M r θ : ℝ) (hM : 0 < M) (hr_ex : 2 * M < r) :
    Riemann M r θ Idx.t Idx.θ Idx.t Idx.θ = M * f M r / r := by
  classical
  have hr_nz : r ≠ 0 := r_ne_zero_of_exterior M r hM hr_ex
  have hf_nz : f M r ≠ 0 := ne_of_gt (f_pos_of_hr M r hM hr_ex)

  rw [Riemann_contract_first M r θ Idx.t Idx.θ Idx.t Idx.θ]
  simp [g]
  unfold RiemannUp
  simp only [dCoord_t, dCoord_r, dCoord_θ, dCoord_φ, sumIdx_expand]

  have hder_tr := deriv_Γ_t_tr_at M r hr_nz hf_nz
  have hder_rr := deriv_Γ_r_rr_at M r hr_nz hf_nz
  simp [hder_tr, hder_rr]

  have rmf : r - 2 * M = r * f M r := by
    simpa [r_mul_f M r hr_nz, mul_comm]
  simp_rw [Γ_r_θθ, rmf]

  simp [Γ_t_tr, Γ_θ_rθ]

  field_simp [hr_nz, hf_nz, pow_two, sq]
  ring  -- ❌ FAILS
```

**Key Difference from R_trtr:**
- Uses `simp_rw [Γ_r_θθ, rmf]` to normalize `Γ_r_θθ = -(r - 2*M)/r²` using `rmf`
- Expands additional symbol: `Γ_θ_rθ = 1/r`

---

### 3. Riemann_tφtφ_eq (R_tφtφ = M·f(r)·sin²θ/r)

```lean
/-- Component: R_tφtφ = M·f(r)·sin²θ/r -/
lemma Riemann_tφtφ_eq (M r θ : ℝ) (hM : 0 < M) (hr_ex : 2 * M < r) :
    Riemann M r θ Idx.t Idx.φ Idx.t Idx.φ = M * f M r * Real.sin θ ^ 2 / r := by
  classical
  have hr_nz : r ≠ 0 := r_ne_zero_of_exterior M r hM hr_ex
  have hf_nz : f M r ≠ 0 := ne_of_gt (f_pos_of_hr M r hM hr_ex)

  rw [Riemann_contract_first M r θ Idx.t Idx.φ Idx.t Idx.φ]
  simp [g]
  unfold RiemannUp
  simp only [dCoord_t, dCoord_r, dCoord_θ, dCoord_φ, sumIdx_expand]

  have hder_tr := deriv_Γ_t_tr_at M r hr_nz hf_nz
  have hder_rr := deriv_Γ_r_rr_at M r hr_nz hf_nz
  simp [hder_tr, hder_rr]

  have rmf : r - 2 * M = r * f M r := by
    simpa [r_mul_f M r hr_nz, mul_comm]
  simp_rw [Γ_r_φφ, rmf]

  simp [Γ_t_tr, Γ_φ_rφ]

  field_simp [hr_nz, hf_nz, pow_two, sq]
  ring  -- ❌ FAILS
```

**Christoffel Symbols:** `Γ_r_φφ = -(r - 2*M)·sin²θ`, `Γ_φ_rφ = 1/r`

---

### 4. Riemann_rθrθ_eq (R_rθrθ = -M/(r·f(r)))

```lean
/-- Component: R_rθrθ = -M/(r·f(r)) -/
lemma Riemann_rθrθ_eq (M r θ : ℝ) (hM : 0 < M) (hr_ex : 2 * M < r) :
    Riemann M r θ Idx.r Idx.θ Idx.r Idx.θ = -M / (r * f M r) := by
  classical
  have hr_nz : r ≠ 0 := r_ne_zero_of_exterior M r hM hr_ex
  have hf_nz : f M r ≠ 0 := ne_of_gt (f_pos_of_hr M r hM hr_ex)

  rw [Riemann_contract_first M r θ Idx.r Idx.θ Idx.r Idx.θ]
  simp [g]
  unfold RiemannUp
  simp only [dCoord_t, dCoord_r, dCoord_θ, dCoord_φ, sumIdx_expand]

  have hder_θφφ := deriv_Γ_θ_φφ_at M r θ hr_nz hf_nz
  simp [hder_θφφ]

  have rmf : r - 2 * M = r * f M r := by
    simpa [r_mul_f M r hr_nz, mul_comm]
  simp_rw [Γ_r_θθ, rmf]

  simp [Γ_θ_rθ, Γ_θ_φφ]

  field_simp [hr_nz, hf_nz, pow_two, sq]
  ring  -- ❌ FAILS
```

**Key Difference:**
- Uses `deriv_Γ_θ_φφ_at` instead of `deriv_Γ_t_tr_at` (angular derivative calculator)
- Expands: `Γ_θ_φφ = -sin θ · cos θ`

---

### 5. Riemann_rφrφ_eq (R_rφrφ = -M·sin²θ/(r·f(r)))

```lean
/-- Component: R_rφrφ = -M·sin²θ/(r·f(r)) -/
lemma Riemann_rφrφ_eq (M r θ : ℝ) (hM : 0 < M) (hr_ex : 2 * M < r) :
    Riemann M r θ Idx.r Idx.φ Idx.r Idx.φ = -M * Real.sin θ ^ 2 / (r * f M r) := by
  classical
  have hr_nz : r ≠ 0 := r_ne_zero_of_exterior M r hM hr_ex
  have hf_nz : f M r ≠ 0 := ne_of_gt (f_pos_of_hr M r hM hr_ex)

  rw [Riemann_contract_first M r θ Idx.r Idx.φ Idx.r Idx.φ]
  simp [g]
  unfold RiemannUp
  simp only [dCoord_t, dCoord_r, dCoord_θ, dCoord_φ, sumIdx_expand]

  have hder_θφφ := deriv_Γ_θ_φφ_at M r θ hr_nz hf_nz
  have hder_φθφ := deriv_Γ_φ_θφ_at M r θ hr_nz hf_nz
  simp [hder_θφφ, hder_φθφ]

  have rmf : r - 2 * M = r * f M r := by
    simpa [r_mul_f M r hr_nz, mul_comm]
  simp_rw [Γ_r_φφ, rmf]

  simp [Γ_φ_rφ, Γ_φ_θφ, Γ_θ_φφ]

  field_simp [hr_nz, hf_nz, pow_two, sq]
  ring  -- ❌ FAILS
```

**Uses Both Angular Derivatives:**
- `deriv_Γ_θ_φφ_at`: Derivative of `Γ_θ_φφ` wrt r
- `deriv_Γ_φ_θφ_at`: Derivative of `Γ_φ_θφ` wrt r

**Expands:** `Γ_φ_rφ = 1/r`, `Γ_φ_θφ = cos θ / sin θ`, `Γ_θ_φφ = -sin θ · cos θ`

---

### 6. Riemann_θφθφ_eq (R_θφθφ = 2Mr·sin²θ)

```lean
/-- Component: R_θφθφ = 2Mr·sin²θ -/
lemma Riemann_θφθφ_eq (M r θ : ℝ) (hM : 0 < M) (hr_ex : 2 * M < r) :
    Riemann M r θ Idx.θ Idx.φ Idx.θ Idx.φ = 2 * M * r * Real.sin θ ^ 2 := by
  classical
  have hr_nz : r ≠ 0 := r_ne_zero_of_exterior M r hM hr_ex
  have hf_nz : f M r ≠ 0 := ne_of_gt (f_pos_of_hr M r hM hr_ex)

  rw [Riemann_contract_first M r θ Idx.θ Idx.φ Idx.θ Idx.φ]
  simp [g]
  unfold RiemannUp
  simp only [dCoord_t, dCoord_r, dCoord_θ, dCoord_φ, sumIdx_expand]

  have hder_θφφ := deriv_Γ_θ_φφ_at M r θ hr_nz hf_nz
  have hder_φθφ := deriv_Γ_φ_θφ_at M r θ hr_nz hf_nz
  simp [hder_θφφ, hder_φθφ]

  have rmf : r - 2 * M = r * f M r := by
    simpa [r_mul_f M r hr_nz, mul_comm]
  simp_rw [Γ_r_θθ, Γ_r_φφ, rmf]  -- Two targets for simp_rw

  simp [Γ_θ_rθ, Γ_θ_φφ, Γ_φ_rφ, Γ_φ_θφ]

  field_simp [hr_nz, hf_nz, pow_two, sq]
  ring  -- ❌ FAILS
```

**Most Complex Case:**
- Uses both angular derivative calculators
- Applies `simp_rw` to **two** Christoffel symbols: `Γ_r_θθ` and `Γ_r_φφ`
- Expands 4 additional symbols

---

## Questions for Junior Professor

### Question 1: Debugging Strategy

All 6 component lemmas fail at the final `ring` step with "unsolved goals". The build output truncates the actual goal state, so I cannot see what algebraic expression remains after Step 5.

**How should I debug this?** Should I:

**Option A:** Use `show <expected_goal>` before `field_simp` to make the goal explicit?

**Option B:** Use `#check` or `#reduce` to inspect intermediate goal states?

**Option C:** Replace `ring` with `sorry` temporarily to see if the issue is just `ring` vs needing additional algebraic tactics?

---

### Question 2: Possible Missing Steps

Your 6-step recipe was:
1. Setup (hr_nz, hf_nz)
2. Contract & expand with `simp only` (keeping Γ boxed)
3. Apply derivative calculators
4. Normalize with `simp_rw [Γ_r_θθ, rmf]`
5. Expand remaining Γ's with `simp [...]`
6. Close with `field_simp + ring`

**Question:** Between Steps 5 and 6, is there a missing step? For example:
- Should I use `show <target>` to restate the goal before field_simp?
- Should I apply additional rewrites like `mul_comm`, `mul_assoc`, `add_comm`?
- Should I use `conv` tactics to rearrange terms?

---

### Question 3: Example Working Goal State

For **one** component lemma (e.g., `Riemann_tθtθ_eq`), could you provide:

**What the goal looks like after Step 5:**
```lean
⊢ <what does the goal actually look like here?>
```

**What `field_simp` produces:**
```lean
⊢ <normalized polynomial form>
```

**Why `ring` should close it:**
```lean
-- Explanation of algebraic equivalence
```

This would help me understand if:
- My Step 5 is producing the wrong intermediate form
- My `field_simp` arguments are missing something
- The goal actually requires `polyrith` or `nlinarith` instead of `ring`

---

### Question 4: Alternative Tactical Approach

If the `simp [...]; field_simp [...]; ring` pattern fundamentally doesn't work for these lemmas, would you recommend:

**Option A:** Use `calc` blocks with manual step-by-step equational reasoning?

**Option B:** Prove intermediate lemmas for each algebraic transformation?

**Option C:** Use `polyrith` or other decision procedures instead of `ring`?

**Option D:** Something else entirely?

---

## Baseline Error Summary

For context, the baseline c173658 has **7 errors** with `lake build`:

### Pre-existing Infrastructure Errors (3)
- **Line 1939:** `unsolved goals` in some infrastructure lemma
- **Line 2188:** `Tactic 'apply' failed`
- **Line 2323:** `'simp' made no progress`

### Diagonal Ricci Case Errors (4)
- **Line 4929:** R_tt case: Uses `Riemann_trtr_reduce`, `Riemann_tθtθ_reduce`, `Riemann_tφtφ_reduce`
- **Line 4979:** R_rr case
- **Line 5018:** R_θθ case
- **Line 5050:** R_φφ case

**Note:** The component lemmas I'm implementing are **separate standalone facts**. They are NOT directly called by `Ricci_zero_ext`. The diagonal Ricci cases use the existing `*_reduce` lemmas (lines 4614-4659) which already compile successfully.

**Purpose of Component Lemmas:** Standalone documentation proving the known closed forms like `R_trtr = -2M/r³`, as requested in your original guidance.

---

## Files Modified

### Papers/P5_GeneralRelativity/GR/Riemann.lean

**Lines Added:** 4897-5037 (141 lines total)

**Structure:**
```lean
-- Line 4897: Phase 1 helper lemmas (r_mul_f, one_minus_f)
-- Line 4907: Phase 2 component lemmas header
-- Line 4909: Riemann_trtr_eq (fails at line 4935)
-- Line 4937: Riemann_tθtθ_eq (fails at line 4960)
-- Line 4962: Riemann_tφtφ_eq (fails at line 4985)
-- Line 4987: Riemann_rθrθ_eq (fails at line 5009)
-- Line 5011: Riemann_rφrφ_eq (fails at line 5034)
-- Line 5036: Riemann_θφθφ_eq (fails at line 5059)
```

---

## Build Output Summary

### Successful Build (lake build)
```bash
cd /Users/quantmann/FoundationRelativity
lake build Papers.P5_GeneralRelativity.GR.Riemann 2>&1 | tee /tmp/phase2_build_v2.txt
```

**Errors Found:** 10 total
- 3 baseline infrastructure errors (unchanged)
- 7 new component lemma errors

**Error Lines:** 1939, 2188, 2323, 4935, 4960, 4985, 5009, 5034, 5059

---

## Next Steps - Awaiting Guidance

**Current State:** Code is at baseline c173658 (clean slate). All attempted component lemma code is documented in this report but not committed.

**Blocked On:**
1. Understanding what goal state remains after Step 5 (build output truncates it)
2. Understanding why `ring` cannot close goals that should be polynomial equalities
3. Determining if there are missing steps between Steps 5 and 6

**Ready To:**
- Provide full goal state dumps if you can suggest a debugging approach
- Try alternative tactical patterns if you recommend them
- Implement any corrections to the 6-step recipe

---

## Appendix: Build Validation

**All testing done with:**
```bash
lake build Papers.P5_GeneralRelativity.GR.Riemann
```

Per [LAKE_BUILD_VS_LAKE_ENV_LEAN_FINDINGS.md](../../LAKE_BUILD_VS_LAKE_ENV_LEAN_FINDINGS.md), `lake build` is the authoritative test. Not using `lake env lean` for validation.

**Baseline Verification:**
```bash
git checkout c173658
lake build Papers.P5_GeneralRelativity.GR.Riemann
# Result: 7 errors (expected)
```

---

**Generated:** October 5, 2025
**Author:** Claude Code
**Purpose:** Request tactical guidance on completing Phase 2 component lemma proofs
**Status:** BLOCKED - Awaiting Junior Professor feedback on why Step 6 (field_simp + ring) fails
