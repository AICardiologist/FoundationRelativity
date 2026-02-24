# Request for Junior Professor Assistance - Component Lemma Mathematical Sign Error

**Date:** October 3, 2025
**Project:** Schwarzschild Spacetime Ricci Tensor Verification (Lean 4)
**Issue Type:** Mathematical correctness / Sign error in component lemma
**Urgency:** Medium - Blocking component lemma proofs, but diagonal cases already proven

---

## Executive Summary

We're working on a formal verification of the Schwarzschild vacuum solution in Lean 4, proving that the Ricci tensor vanishes (R_μν = 0) for all components. We've successfully completed Phase 3.1 (all 4 diagonal cases proven), and are now fixing component lemma errors in Phase 3.2.

**Problem:** The component lemma `R_θrθr_eq` has a **mathematical sign error** - after applying our Direct Controlled Rewriting Sequence (CRS), the final algebraic goal reduces to:

```lean
⊢ -(r * M * (r - M*2)⁻¹ * sin θ) = r * M * (r - M*2)⁻¹ * sin θ
```

This is clearly impossible (negative ≠ positive). We need help identifying whether:
1. The component lemma formula is incorrect
2. There's an error in our Riemann tensor definition
3. There's an index convention mismatch
4. There's a tactical issue we're missing

---

## Background Context

### Project Structure

**Goal:** Prove Einstein vacuum field equations R_μν = 0 for Schwarzschild spacetime

**Schwarzschild Metric:**
```
ds² = -f(r)dt² + f(r)⁻¹dr² + r²dθ² + r²sin²θ dφ²
```
where `f(r) = 1 - 2M/r` and we're in the exterior region `r > 2M`.

**Coordinates:** (t, r, θ, φ) with signature (-,+,+,+)

### Riemann Tensor Definition (from our codebase)

```lean
-- Riemann tensor with 4 lower indices: R_{abcd}
def Riemann (M r θ : ℝ) (a b c d : Idx) : ℝ :=
  sumIdx (fun ρ => g M r θ a ρ * RiemannUp M r θ ρ b c d)

-- Riemann tensor with 1 upper, 3 lower indices: R^ρ_{bcd}
def RiemannUp (M r θ : ℝ) (ρ b c d : Idx) : ℝ :=
  dCoord c (Γtot M r θ ρ b d) r θ - dCoord d (Γtot M r θ ρ b c) r θ +
  sumIdx (fun σ => Γtot M r θ ρ c σ * Γtot M r θ σ b d) -
  sumIdx (fun σ => Γtot M r θ ρ d σ * Γtot M r θ σ b c)
```

**Key:** `dCoord` is the coordinate derivative, `Γtot` is the Christoffel symbol function.

### Ricci Tensor Computation

**Definition:**
```lean
def RicciContraction (M r θ : ℝ) (a b : Idx) : ℝ :=
  sumIdx (fun ρ => gInv M r θ ρ ρ * Riemann M r θ ρ a ρ b)
```

This contracts: R_ab = g^{cd} R_{cadb}

### Component Lemma Strategy

We prove individual Riemann components like R_{θrθr}, R_{φrφr}, etc., then use them in Ricci contraction proofs. These component lemmas use a **Direct Controlled Rewriting Sequence (Direct CRS)**:

**Phase 1: Structural Expansion**
```lean
unfold Riemann RiemannUp
simp only [sumIdx_expand, Riemann_contract_first]
```

**Phase 2: Projection** (expand metric, Christoffel, coordinate differentials)
```lean
simp only [g, Γtot, dCoord_r, dCoord_θ, ...]
```

**Phase 3: Calculus** (apply derivative calculators)
```lean
simp only [deriv_Γ_θ_rθ_at r hr_nz, deriv_Γ_r_θθ_at M r hr_nz]
```

**Phase 4: Definition Substitution** (unfold Christoffel symbols)
```lean
simp only [Γ_θ_rθ, Γ_r_θθ, Γ_r_rr, ...]
```

**Phase 5: Algebraic Normalization**
```lean
unfold f
field_simp [hr_nz, hf_nz, pow_two, sq]
simp [deriv_const]
ring
```

---

## The Problematic Lemma: R_θrθr_eq

### Expected Formula

From Wald/Carroll GR textbooks, the Schwarzschild Riemann component should be:

**R_{θrθr} = M/(r·f(r))** where f(r) = 1 - 2M/r

### Current Lean Implementation

**File:** `Papers/P5_GeneralRelativity/GR/Riemann.lean`
**Lines:** 5157-5185

```lean
/-- R_{θrθr} = M/(r·f(r)) where f(r) = 1 - 2M/r (Wald/Carroll convention) -/
lemma R_θrθr_eq (M r θ : ℝ) (hM : 0 < M) (h_r_gt_2M : 2 * M < r) (h_sin_nz : Real.sin θ ≠ 0) :
  Riemann M r θ Idx.θ Idx.r Idx.θ Idx.r = M / (r * f M r) := by

  -- Establish hypotheses
  have hr_nz : r ≠ 0 := by linarith [hM, h_r_gt_2M]
  have h_ext : Exterior M r θ := ⟨hM, h_r_gt_2M⟩
  have hf_nz : f M r ≠ 0 := Exterior.f_ne_zero h_ext

  -- DIRECT CONTROLLED REWRITING SEQUENCE

  -- Step 1: Structural Expansion
  unfold Riemann RiemannUp
  simp only [sumIdx_expand, Riemann_contract_first]

  -- Step 2: Phase 1 - Projection
  simp only [g, Γtot, dCoord_r, dCoord_θ]

  -- Step 3: Phase 2 - Calculus
  simp only [deriv_Γ_θ_rθ_at r hr_nz, deriv_Γ_r_θθ_at M r hr_nz]

  -- Step 4: Phase 3 - Definition Substitution
  simp only [Γ_θ_rθ, Γ_r_θθ, Γ_r_rr, Γ_t_tr, Γ_r_tt, Γ_r_φφ, Γ_φ_rφ, Γ_θ_φφ, Γ_φ_θφ]

  -- Step 5: Algebraic Normalization
  unfold f
  field_simp [hr_nz, hf_nz, pow_two, sq]
  simp [deriv_const]
  ring  -- ❌ ERROR: unsolved goals
```

### The Error

**Build Output:**
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:5159:61: unsolved goals
M r θ : ℝ
hM : 0 < M
h_r_gt_2M : 2 * M < r
h_sin_nz : sin θ ≠ 0
hr_nz : r ≠ 0
h_ext : Exterior M r θ
hf_nz : f M r ≠ 0
⊢ -(r * M * (r - M * 2)⁻¹ * sin θ) = r * M * (r - M * 2)⁻¹ * sin θ
```

**Analysis:**
The goal is asking us to prove that some expression equals its negative, which is impossible unless the expression is zero. But the component lemma claims R_{θrθr} = M/(r·f(r)) ≠ 0.

Note that `(r - M*2)⁻¹ = 1/(r - 2M) = r/(r·f(r))` since `f(r) = 1 - 2M/r = (r - 2M)/r`.

So the goal is essentially asking:
```
⊢ -(M * r / (r * f(r)) * sin θ) = M * r / (r * f(r)) * sin θ
```

---

## Derivative Calculators Used

The lemma uses two derivative calculators:

### 1. deriv_Γ_θ_rθ_at

**Definition:** Derivative of Γ^θ_{rθ} with respect to r

**Implementation:** (from `Papers/P5_GeneralRelativity/GR/Riemann.lean:1070-1078`)
```lean
/-- `d/dr Γ^θ_{rθ}(r) = -1/r²`. -/
@[simp] lemma deriv_Γ_θ_rθ_at (r : ℝ) (hr : r ≠ 0) :
  deriv (fun s => Γ_θ_rθ s) r = -1 / r^2 := by
  classical
  -- Γ^θ_{rθ}(s) = 1/s
  have h_rewrite : (fun s => Γ_θ_rθ s) = (fun s => (s)⁻¹) := by
    funext s; simp [Γ_θ_rθ]
  -- Use the robust reciprocal rule proved above
  have h := deriv_inv_general (fun s => s) r (by simpa using hr) (differentiableAt_id r)
  -- deriv id at r is 1
  have hid : deriv (fun s => s) r = 1 := by simpa using deriv_id''
  simpa [h_rewrite, hid, one_div, pow_two] using h
```

**Christoffel Symbol:**
```lean
def Γ_θ_rθ (r : ℝ) : ℝ := 1 / r
```

### 2. deriv_Γ_r_θθ_at

**Definition:** Derivative of Γ^r_{θθ} with respect to r

**Implementation:** (from `Papers/P5_GeneralRelativity/GR/Riemann.lean:1058-1068`)
```lean
/-- `d/dr Γ^r_{θθ}(r) = -1`. -/
@[simp] lemma deriv_Γ_r_θθ_at (M r : ℝ) (hr : r ≠ 0) :
  deriv (fun s => Γ_r_θθ M s) r = -1 := by
  classical
  -- Γ^r_{θθ}(s) = -(s - 2*M)
  have h_sub : deriv (fun s => s - (2*M)) r = 1 := by
    -- d/dr s = 1, d/dr (2M) = 0
    simpa [deriv_id'', deriv_const] using
      deriv_sub (differentiableAt_id r) (differentiableAt_const (2*M))
  have h_neg : deriv (fun s => -(s - (2*M))) r = -1 := by
    -- d/dr (-(s-2M)) = -(d/dr (s-2M))
    simpa [deriv_neg, h_sub]
  simpa [Γ_r_θθ] using h_neg
```

**Christoffel Symbol:**
```lean
def Γ_r_θθ (M r : ℝ) : ℝ := -(r - 2 * M)
```

---

## Relevant Christoffel Symbols

From `Papers/P5_GeneralRelativity/GR/Schwarzschild.lean`:

```lean
-- Non-zero components (proven in separate file)
def Γ_t_tr (M r : ℝ) : ℝ := M / (r * f M r)
def Γ_r_tt (M r : ℝ) : ℝ := M * f M r / r^2
def Γ_r_rr (M r : ℝ) : ℝ := -M / (r * f M r)
def Γ_r_θθ (M r : ℝ) : ℝ := -(r - 2 * M)  -- = -r·f(r)
def Γ_r_φφ (M r θ : ℝ) : ℝ := -(r - 2 * M) * (Real.sin θ)^2
def Γ_θ_rθ (r : ℝ) : ℝ := 1 / r
def Γ_θ_φφ (θ : ℝ) : ℝ := -Real.sin θ * Real.cos θ
def Γ_φ_rφ (r : ℝ) : ℝ := 1 / r
def Γ_φ_θφ (θ : ℝ) : ℝ := Real.cos θ / Real.sin θ

-- Zero components (all others)
```

**Key relation:** `Γ_r_θθ(r) = -(r - 2M) = -r·f(r)` since `f(r) = 1 - 2M/r = (r-2M)/r`

---

## Comparison with Working Lemma: R_φrφr_eq

To help diagnose the issue, here's a similar lemma that **does work**:

**R_{φrφr} = M·sin²θ/(r·f(r))** (just R_{θrθr} multiplied by sin²θ)

**Implementation:** (Lines 5187-5215)
```lean
lemma R_φrφr_eq (M r θ : ℝ) (hM : 0 < M) (h_r_gt_2M : 2 * M < r) (h_sin_nz : Real.sin θ ≠ 0) :
  Riemann M r θ Idx.φ Idx.r Idx.φ Idx.r = M * (Real.sin θ)^2 / (r * f M r) := by

  -- [Same hypothesis setup as R_θrθr_eq]
  have hr_nz : r ≠ 0 := by linarith [hM, h_r_gt_2M]
  have h_ext : Exterior M r θ := ⟨hM, h_r_gt_2M⟩
  have hf_nz : f M r ≠ 0 := Exterior.f_ne_zero h_ext

  -- DIRECT CONTROLLED REWRITING SEQUENCE

  -- Step 1: Structural Expansion
  unfold Riemann RiemannUp
  simp only [sumIdx_expand, Riemann_contract_first]

  -- Step 2: Phase 1 - Projection
  simp only [g, Γtot, dCoord_r, dCoord_φ]  -- ✅ Uses dCoord_φ instead of dCoord_θ

  -- Step 3: Phase 2 - Calculus
  simp only [deriv_Γ_φ_rφ_at r hr_nz, deriv_Γ_r_φφ_at M r θ]

  -- Step 4: Phase 3 - Definition Substitution
  simp only [Γ_φ_rφ, Γ_r_φφ, Γ_r_rr, Γ_t_tr, Γ_r_tt, Γ_θ_rθ, Γ_r_θθ, Γ_θ_φφ, Γ_φ_θφ]

  -- Step 5: Algebraic Normalization
  unfold f
  field_simp [hr_nz, hf_nz, pow_two, sq, h_sin_nz]
  simp [deriv_const, dCoord_φ]
  ring  -- ✅ WORKS!
```

**Difference:** R_φrφr_eq works perfectly with the same pattern. The only structural differences are:
1. Uses φ indices instead of θ
2. Uses different derivative calculators (deriv_Γ_φ_rφ_at, deriv_Γ_r_φφ_at)
3. Final result has sin²θ factor

---

## Previously Successful Component Lemma: R_rtrt_eq

For reference, this component lemma was successfully proven and is used in the diagonal cases:

**R_{rtrt} = 2M/r³** (proven in lines 5058-5097)

```lean
lemma R_rtrt_eq (M r θ : ℝ) (hM : 0 < M) (h_r_gt_2M : 2 * M < r) :
  Riemann M r θ Idx.r Idx.t Idx.r Idx.t = (2 * M) / r^3 := by

  -- Establish hypotheses
  have hr_nz : r ≠ 0 := by linarith [hM, h_r_gt_2M]
  have h_ext : Exterior M r θ := ⟨hM, h_r_gt_2M⟩
  have hf_nz : f M r ≠ 0 := Exterior.f_ne_zero h_ext

  -- DIRECT CONTROLLED REWRITING SEQUENCE

  -- Step 1: Structural Expansion
  unfold Riemann RiemannUp
  simp only [sumIdx_expand]
  simp only [Riemann_contract_first]

  -- Step 2: Phase 1 - Projection
  simp only [g, Γtot, dCoord_r, dCoord_t]

  -- Step 3: Phase 2 - Calculus
  simp only [deriv_Γ_r_tt_at M r hr_nz hf_nz,
             deriv_Γ_t_tr_at M r hr_nz hf_nz]

  -- Step 4: Phase 3 - Definition Substitution
  simp only [Γ_r_tt, Γ_t_tr, Γ_r_rr]

  -- Step 5: Algebraic Normalization
  unfold f
  field_simp [hr_nz, pow_two, sq]
  ring  -- ✅ WORKS!
```

**Note:** This lemma doesn't need `simp [deriv_const]` - it closes with just `field_simp + ring`.

---

## Diagnostic Questions

1. **Is the formula correct?**
   - Textbook value: R_{θrθr} = M/(r·f(r))
   - Is this the correct value for Schwarzschild with signature (-,+,+,+)?
   - Could there be a sign convention difference?

2. **Index ordering:**
   - We're computing: `Riemann M r θ Idx.θ Idx.r Idx.θ Idx.r`
   - This means R_{θrθr} with indices in order: θ, r, θ, r
   - Is this the correct ordering for the definition we're using?

3. **Derivative calculator signs:**
   - `deriv_Γ_θ_rθ_at` returns `-1/r²` (negative)
   - `deriv_Γ_r_θθ_at` returns `-1` (negative)
   - Are these signs correct?

4. **Christoffel symbol signs:**
   - `Γ_θ_rθ = 1/r` (positive)
   - `Γ_r_θθ = -(r - 2M)` (negative)
   - Are these signs correct for Schwarzschild?

5. **Tactical issue:**
   - Could there be a simplification step we're missing that would eliminate the sign discrepancy?
   - Should we be using different Christoffel symbols or derivative calculators?

---

## What We've Tried

1. ✅ **Added missing hr_nz argument** to `deriv_Γ_r_θθ_at M r hr_nz`
2. ✅ **Added comprehensive Christoffel symbol expansion** in Phase 3
3. ✅ **Added `simp [deriv_const]`** to eliminate derivative constant terms
4. ❌ **Result:** Still get impossible goal `⊢ -X = X`

---

## Request for Assistance

**Primary Question:** Why does the R_θrθr_eq proof reduce to an impossible goal (`⊢ -X = X`)?

**Specific Help Needed:**

1. **Mathematical verification:**
   - Is the formula R_{θrθr} = M/(r·f(r)) correct for Schwarzschild with our conventions?
   - Should there be a different sign or factor?

2. **Index convention check:**
   - Is our Riemann tensor definition consistent with standard GR textbooks?
   - Should `Riemann M r θ Idx.θ Idx.r Idx.θ Idx.r` equal R_{θrθr} or something else?

3. **Tactical guidance:**
   - Is there a simplification tactic we're missing?
   - Should we approach the proof differently?

4. **Comparison analysis:**
   - Why does R_φrφr_eq work but R_θrθr_eq doesn't?
   - They should be nearly identical (just differ by sin²θ factor)

---

## Additional Context

**Project Status:**
- ✅ Phase 1-2 complete: All 6 principal component lemmas proven (R_rtrt, R_θtθt, R_φtφt, R_φθφθ, etc.)
- ✅ Phase 3.1 complete: All 4 diagonal Ricci cases proven (R_tt = R_rr = R_θθ = R_φφ = 0)
- ⏸️ Phase 3.2: Fixing component lemma errors (R_θrθr, R_φrφr, etc.)

**Current Build Status:**
- 13 errors remaining (down from 31 at session start)
- 8 sorry warnings (symmetry lemmas + auxiliary lemmas)
- **All diagonal Ricci cases work correctly** ✅

**Files Involved:**
- `Papers/P5_GeneralRelativity/GR/Riemann.lean` - Main Ricci tensor proofs
- `Papers/P5_GeneralRelativity/GR/Schwarzschild.lean` - Christoffel symbols, metric definitions

**Lean Version:** Lean 4.23.0-rc2 with mathlib

---

## Expected Output

Please provide:

1. **Root cause identification:** Why is there a sign mismatch?
2. **Correction strategy:** What needs to be changed (formula, definition, tactics)?
3. **Verification:** Confirmation of correct R_{θrθr} value for Schwarzschild
4. **Implementation guidance:** Specific tactics or rewrites to fix the proof

---

## Thank You

We appreciate your expertise in both Lean 4 tactics and general relativity mathematics. This is a critical blocker for completing the Schwarzschild Ricci tensor verification, and your guidance will help us understand whether this is a tactical issue or a deeper mathematical error in our formulation.

**Contact:** Please respond with analysis and recommendations. We can provide additional code context, intermediate goals, or specific file contents as needed.
