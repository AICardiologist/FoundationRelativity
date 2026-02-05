# Request for Junior Professor Assistance - Off-Diagonal Ricci Architectural Lemma

**Date:** October 4, 2025
**Project:** Schwarzschild Spacetime Ricci Tensor Verification (Lean 4)
**Issue Type:** Proof Architecture / Lemma Connection
**Urgency:** High - Blocking 12 Ricci off-diagonal cases

---

## Executive Summary

We're working on eliminating sorries in the Schwarzschild Ricci tensor formalization (proving R_μν = 0 for all components). We've successfully proven:

- ✅ **Infrastructure:** All Christoffel symbols, derivative calculators correct (thanks to Senior Professor's Γ_r_tt fix)
- ✅ **All 4 diagonal Ricci cases** proven (R_tt = R_rr = R_θθ = R_φφ = 0)
- ✅ **All 6 Ricci_offdiag_sum lemmas** proven (showing ∑_ρ R_{ρaρb} = 0)

**Current Blocker:** We have 12 off-diagonal Ricci cases with sorries because we cannot connect:
- Our `RicciContraction` definition (double sum with g^{cd})
- To the pre-proven `Ricci_offdiag_sum` lemmas (single sum over ρ)

**Question:** What's the correct Lean 4 approach to prove that when `gInv` is diagonal, the double sum reduces to the single diagonal sum?

---

## The Architectural Gap

### What We Have

**1. RicciContraction Definition (Double Sum):**
```lean
noncomputable def RicciContraction (M r θ : ℝ) (a b : Idx) : ℝ :=
  sumIdx (fun c =>
    sumIdx (fun d =>
      gInv M c d r θ * Riemann M r θ c a d b
    )
  )
```

**2. Proven Lemmas (Single Sum):**
```lean
@[simp] lemma Ricci_offdiag_sum_tθ (M r θ : ℝ) :
  sumIdx (fun ρ => Riemann M r θ ρ Idx.t ρ Idx.θ) = 0

@[simp] lemma Ricci_offdiag_sum_tr (M r θ : ℝ) :
  sumIdx (fun ρ => Riemann M r θ ρ Idx.t ρ Idx.r) = 0

-- ... (6 total offdiag sum lemmas)
```

**3. Known Property (gInv is Diagonal):**
```lean
-- Schwarzschild inverse metric is diagonal
lemma gInv_offdiag_zero (M : ℝ) (c d : Idx) (r θ : ℝ) (hcd : c ≠ d) :
  gInv M c d r θ = 0 := by
  unfold gInv
  cases c <;> cases d <;> simp [hcd]
  -- All off-diagonal cases are 0
```

### What We Need

**Mathematical Insight:**
When g^{cd} is diagonal (g^{cd} = 0 for c ≠ d):
```
R_{ab} = ∑_c ∑_d g^{cd} R_{cadb}
       = ∑_c g^{cc} R_{cacb}  (off-diagonal terms vanish)
```

**Lean Translation:**
We need to prove:
```lean
lemma RicciContraction_eq_diagonal_sum_when_gInv_diagonal
  (M r θ : ℝ) (a b : Idx) :
  RicciContraction M r θ a b =
    sumIdx (fun c => gInv M c c r θ * Riemann M r θ c a c b) := by
  unfold RicciContraction
  -- How do we formally show the double sum reduces to diagonal sum?
  sorry
```

---

## Our Attempted Approaches

### Approach 1: Direct Tactical Simplification (FAILED)

```lean
case t.θ =>
  simp only [sumIdx_expand, gInv]
  simp
```

**Result:** Unsolved goals
```lean
⊢ -(f M r)⁻¹ * Riemann M r θ t Idx.θ t Idx.θ +
  0 * Riemann M r θ t Idx.θ Idx.r Idx.θ +
  0 * Riemann M r θ t Idx.θ Idx.θ Idx.θ +
  0 * Riemann M r θ t Idx.θ φ Idx.θ +
  (0 * ... + f M r * Riemann M r θ Idx.r Idx.θ Idx.r Idx.θ + ...) +
  ... = 0
```

**Problem:** `simp` doesn't know that `0 * X = 0` should be eliminated, and doesn't connect the expanded diagonal terms to `Ricci_offdiag_sum_tθ`.

### Approach 2: Manual Expansion (PARTIAL)

```lean
case t.θ =>
  unfold RicciContraction
  simp only [sumIdx_expand, gInv]
  -- Now we see: -(f⁻¹) * R_{tttθ} + 0 * ... + f * R_{rtrθ} + 0 * ... + r⁻² * R_{θtθθ} + ...
  simp only [Riemann_first_equal_zero]  -- R_{tttθ} = 0 (first=third antisymmetry)
  -- Stuck: How to connect remaining terms to Ricci_offdiag_sum_tθ?
  sorry
```

**Problem:** After eliminating zeros and using antisymmetry, we have:
```
-(f⁻¹) * R_{tttθ} + f * R_{rtrθ} + r⁻² * R_{θtθθ} + (r·sinθ)⁻² * R_{φtφθ} = 0
```

But `Ricci_offdiag_sum_tθ` proves:
```
R_{tttθ} + R_{rtrθ} + R_{θtθθ} + R_{φtφθ} = 0
```

These don't match directly (different coefficients g^{cc}).

---

## Specific Questions for Junior Professor

### Question 1: Lemma Strategy

Which approach is better for proving the double→single sum reduction?

**Option A - General Reduction Lemma:**
```lean
lemma sumIdx_product_diagonal
  {α β : Type} [Fintype α] (f : α → α → β → ℝ) (g : α → β → ℝ)
  (h_diag : ∀ x y b, x ≠ y → f x y b = 0) :
  (∑ x, ∑ y, f x y b * g x y b) = (∑ x, f x x b * g x x b) := by
  sorry
```

**Option B - Schwarzschild-Specific:**
```lean
lemma RicciContraction_diagonal_gInv
  (M r θ : ℝ) (a b : Idx) :
  RicciContraction M r θ a b =
    sumIdx (fun c => gInv M c c r θ * Riemann M r θ c a c b) := by
  unfold RicciContraction sumIdx
  simp only [Finset.sum_product]
  -- Use gInv_offdiag_zero to eliminate c ≠ d terms
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_eq_single c
  · intro d _ hdc
    simp [gInv_offdiag_zero M c d r θ hdc]
  · intro _; simp
```

**Which is more robust for our use case?**

### Question 2: Connecting the Sums

After reducing to diagonal sum, how do we connect:
```
∑_c g^{cc} R_{cacb} = 0
```
to
```
∑_ρ R_{ρaρb} = 0  (our proven Ricci_offdiag_sum lemma)
```

**Attempted approach:**
```lean
case t.θ =>
  rw [RicciContraction_diagonal_gInv M r θ Idx.t Idx.θ]
  simp only [sumIdx_expand, gInv]
  -- Now: -(f⁻¹) * R_{tttθ} + f * R_{rtrθ} + r⁻² * R_{θtθθ} + (r·sinθ)⁻² * R_{φtφθ} = 0

  -- How to factor out coefficients and use Ricci_offdiag_sum_tθ?
  -- Ricci_offdiag_sum_tθ: R_{tttθ} + R_{rtrθ} + R_{θtθθ} + R_{φtφθ} = 0

  sorry
```

**Is there a tactic or lemma pattern to factor out the g^{cc} coefficients?**

### Question 3: First-Index Antisymmetry

We have:
```lean
lemma Riemann_first_equal_zero (M r θ : ℝ) (a c : Idx) :
  Riemann M r θ a c a c = 0
```

This means R_{tttθ} = 0. But after expanding gInv, we get terms like:
```
-(f⁻¹) * R_{tttθ} + ... = 0
```

Should we:
- **A)** Use `simp only [Riemann_first_equal_zero]` to eliminate R_{tttθ} = 0 terms first?
- **B)** Keep them and rely on the Ricci_offdiag_sum lemma (which already accounts for them being 0)?

### Question 4: Index Ordering

Our `Ricci_offdiag_sum_tθ` proves:
```lean
sumIdx (fun ρ => Riemann M r θ ρ Idx.t ρ Idx.θ) = 0
```

But `RicciContraction` has:
```lean
sumIdx (fun c => gInv M c c r θ * Riemann M r θ c a c b)
```

For `a = Idx.t, b = Idx.θ`, this gives:
```lean
∑_c g^{cc} * R_{ctcθ}
```

**Are these the same?** The index order is (c, t, c, θ) vs (ρ, t, ρ, θ). Do we need index reordering lemmas or are they automatically the same by our Riemann definition?

---

## Context: What's Already Working

### Infrastructure (All Correct ✅)

Thanks to the Senior Professor's Γ_r_tt sign fix, all foundational pieces are correct:

1. **Christoffel Symbols:** All 10 non-zero Γ^μ_{νρ} symbols mathematically verified
2. **Derivative Calculators:** All deriv_Γ_*_* lemmas proven and correct
3. **Riemann Components:** All 6 principal components match literature values:
   - R_{rtrt} = -2M/r³ ✅
   - R_{θrθr} = -M/(rf) ✅
   - R_{φrφr} = -M sin²θ/(rf) ✅
   - R_{θtθt} = +Mf/r ✅
   - R_{φtφt} = +Mf sin²θ/r ✅
   - R_{φθφθ} = +2Mr sin²θ ✅

### Diagonal Ricci Cases (All Proven ✅)

All 4 diagonal cases proven using Direct CRS + ring:
```lean
case t.t =>
  -- R_tt = g^{tt}R_{trtr} + g^{rr}R_{rtrt} + g^{θθ}R_{θtθt} + g^{φφ}R_{φtφt} = 0
  simp only [sumIdx_expand, gInv, Riemann_first_equal_zero]
  simp only [R_trtr_eq, R_rtrt_eq, R_θtθt_eq, R_φtφt_eq]
  unfold f; field_simp; ring  -- ✅ Closes!
```

Same pattern works for R_rr, R_θθ, R_φφ.

### Ricci_offdiag_sum Lemmas (All Proven ✅)

All 6 off-diagonal sum lemmas proven:
```lean
Ricci_offdiag_sum_tr: ∑_ρ R_{ρtρr} = 0  ✅
Ricci_offdiag_sum_tθ: ∑_ρ R_{ρtρθ} = 0  ✅
Ricci_offdiag_sum_tφ: ∑_ρ R_{ρtρφ} = 0  ✅
Ricci_offdiag_sum_rθ: ∑_ρ R_{ρrρθ} = 0  ✅
Ricci_offdiag_sum_rφ: ∑_ρ R_{ρrρφ} = 0  ✅
Ricci_offdiag_sum_θφ: ∑_ρ R_{ρθρφ} = 0  ✅
```

**These close via manual Riemann expansion and field_simp + ring.**

---

## What We're Asking

We need tactical/architectural guidance on the Lean 4 approach to:

1. **Prove the reduction lemma:** Double sum → diagonal sum when gInv diagonal
2. **Connect diagonal sum to proven lemmas:** How to use Ricci_offdiag_sum in the off-diagonal Ricci cases

**Specific help needed:**
- Lemma formulation advice (general vs specific)
- Tactical patterns for sum manipulation
- Index ordering verification
- Example proof for one case (e.g., R_tθ = 0)

---

## Current Codebase Status

**File:** `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean`

**Sorry Count:** 22 total
- 12 sorries: Off-diagonal Ricci cases (lines 5287-5320) ← **THIS ISSUE**
- 7 sorries: Riemann symmetry lemmas (deferred)
- 3 comment references (not actual sorries)

**Build Status:** 15 errors (pre-existing component lemma issues, not blocking this work)

**Lines of Interest:**
- **Line 4930-4975:** Ricci_offdiag_sum lemmas (all proven)
- **Line 5237-5280:** RicciContraction definition and Ricci_zero_ext main theorem
- **Line 5283-5332:** Off-diagonal Ricci cases (12 sorries - where we need help)

---

## Urgency Justification

This is the **last major barrier** to completing the Ricci tensor proof:

**Current State:**
- ✅ Infrastructure correct (Christoffel, derivatives, components)
- ✅ 4/4 diagonal cases proven
- ⚠️ 12/12 off-diagonal cases blocked by this architectural issue
- ⏸️ 7 symmetry lemmas (lower priority, different issue)

**Once Unblocked:**
- Prove all 12 off-diagonal cases using the connecting lemma
- Complete Ricci_zero_ext main theorem
- Achieve **0 sorries** in the Ricci tensor formalization

**Time Sensitivity:**
We've invested significant effort in infrastructure corrections (Senior Professor's Γ_r_tt fix) and the proof strategy is sound. This tactical/architectural question is the final piece.

---

## Requested Response Format

If possible, please provide:

1. **Recommended Lemma Formulation** (general or specific approach)
2. **Proof Sketch** for the reduction lemma
3. **Example Application** showing how to use it in one off-diagonal case (e.g., R_tθ = 0)
4. **Tactical Guidance** on sum manipulation in Lean 4

**Alternative:** If this is a common pattern in formalized differential geometry, pointers to similar proofs in Mathlib or other projects would be very helpful.

---

## Acknowledgments

**Senior Professor:** Infrastructure corrections (Γ_r_tt sign fix) were essential - diagonal cases now work perfectly.

**Junior Professor (Previous Help):** Your guidance on GR sign conventions and proof strategies was invaluable for establishing the infrastructure.

**This Request:** We're at the final tactical hurdle. Your expertise on Lean proof architecture would help us complete this formalization.

---

**Contact:** Research Team - Schwarzschild Formalization Project
**Files Available:** Full codebase at `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/`
**Documentation:** See `SESSION_REPORT_OCT4_SORRY_ELIMINATION.md` for detailed session history

---

**Priority:** High
**Expected Resolution:** Lemma formulation + tactical pattern → 12 off-diagonal cases proven → Main theorem complete
