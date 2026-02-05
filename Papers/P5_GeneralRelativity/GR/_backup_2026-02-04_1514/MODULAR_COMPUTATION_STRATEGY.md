# Modular Computation Strategy - Implementation Plan

**Based On:** Senior Professor's Framework Guidance (October 5, 2025)
**Status:** Ready to implement
**Target:** Fix all 7 errors in c173658 using modular approach

---

## Executive Summary

**The Problem:** Current c173658 uses "Big Bang" approach - expanding all definitions into one monolithic expression. Too complex for automated tactics.

**The Solution:** **Modular Computation** (standard GR textbook approach)
1. Algebraic helper lemmas for f(r) identities
2. Independent Riemann component lemmas (6 components)
3. Refactor Ricci_zero_ext to use component lemmas

**Key Insight:** The f4e134f auxiliary lemma approach was **correct strategy**, it just had **wrong formulas**. Now we have the correct formulas from Senior Professor.

---

## Phase 1: Algebraic Helper Lemmas

**Location:** Add to Schwarzschild.lean (near f(r) definition)

### Lemma 1: r_mul_f
```lean
/-- r · f(r) = r - 2M -/
lemma r_mul_f (M r : ℝ) : r * f M r = r - 2*M := by
  simp [f]
  ring
```

### Lemma 2: f_deriv
```lean
/-- ∂_r f(r) = 2M / r² -/
lemma f_deriv (M r : ℝ) (hr_nz : r ≠ 0) :
  deriv (fun s => f M s) r = 2*M / r^2 := by
  -- f(r) = 1 - 2M/r
  have hf : (fun s => f M s) = (fun s => 1 - 2*M/s) := by
    funext s; simp [f]
  rw [hf]
  -- derivative of 1 - 2M/r
  have : deriv (fun s => 1 - 2*M/s) r = 2*M/r^2 := by
    sorry -- Junior Professor can help with HasDerivAt proof
  exact this
```

### Lemma 3: one_minus_f
```lean
/-- 1 - f(r) = 2M/r -/
lemma one_minus_f (M r : ℝ) (hr_nz : r ≠ 0) :
  1 - f M r = 2*M / r := by
  simp [f]
  field_simp [hr_nz]
  ring
```

**Priority:** HIGH (needed for component lemmas)
**Difficulty:** LOW (simple algebra)
**Action:** Implement immediately

---

## Phase 2: Six Independent Riemann Component Lemmas

**Location:** Add to Riemann.lean (before Ricci_zero_ext)

**Note:** These are the **correct formulas** from Senior Professor, replacing the incorrect ones from f4e134f.

### Component 1: R_trtr
```lean
/-- Schwarzschild Riemann component R_{trtr} = -2M/r³ -/
lemma Riemann_trtr_eq (M r θ : ℝ) (hM : 0 < M) (hr_ex : 2 * M < r) :
  Riemann M r θ Idx.t Idx.r Idx.t Idx.r = -2*M / r^3 := by
  -- Expand Riemann definition
  unfold Riemann
  -- Use diagonal metric collapse
  simp only [sumIdx_expand, g]
  -- Expand in terms of Christoffel symbols and derivatives
  simp only [RiemannUp, dCoord_r, dCoord_t]
  -- Use derivative calculator lemmas
  simp only [deriv_Γ_t_tr, deriv_Γ_r_rr]
  -- Algebraic simplification
  have hr_nz : r ≠ 0 := by linarith
  have hf_nz : f M r ≠ 0 := by
    sorry -- f(r) > 0 in exterior region
  have hr2M : r - 2*M ≠ 0 := by linarith
  -- Apply helper lemmas
  simp only [r_mul_f, one_minus_f hr_nz]
  -- Final algebra
  field_simp [hr_nz, hf_nz, hr2M]
  ring
```

### Component 2: R_tθtθ
```lean
/-- Schwarzschild Riemann component R_{tθtθ} = M·f(r)/r -/
lemma Riemann_tθtθ_eq (M r θ : ℝ) (hM : 0 < M) (hr_ex : 2 * M < r) :
  Riemann M r θ Idx.t Idx.θ Idx.t Idx.θ = M * f M r / r := by
  sorry -- Similar structure to R_trtr
```

### Component 3: R_tφtφ
```lean
/-- Schwarzschild Riemann component R_{tφtφ} = M·f(r)·sin²θ/r -/
lemma Riemann_tφtφ_eq (M r θ : ℝ) (hM : 0 < M) (hr_ex : 2 * M < r) :
  Riemann M r θ Idx.t Idx.φ Idx.t Idx.φ = M * f M r * (Real.sin θ)^2 / r := by
  sorry -- Similar structure to R_trtr
```

### Component 4: R_rθrθ
```lean
/-- Schwarzschild Riemann component R_{rθrθ} = -M/(r·f(r)) -/
lemma Riemann_rθrθ_eq (M r θ : ℝ) (hM : 0 < M) (hr_ex : 2 * M < r) :
  Riemann M r θ Idx.r Idx.θ Idx.r Idx.θ = -M / (r * f M r) := by
  sorry -- Similar structure to R_trtr
```

### Component 5: R_rφrφ
```lean
/-- Schwarzschild Riemann component R_{rφrφ} = -M·sin²θ/(r·f(r)) -/
lemma Riemann_rφrφ_eq (M r θ : ℝ) (hM : 0 < M) (hr_ex : 2 * M < r) :
  Riemann M r θ Idx.r Idx.φ Idx.r Idx.φ = -M * (Real.sin θ)^2 / (r * f M r) := by
  sorry -- Similar structure to R_trtr
```

### Component 6: R_θφθφ
```lean
/-- Schwarzschild Riemann component R_{θφθφ} = 2Mr·sin²θ -/
lemma Riemann_θφθφ_eq (M r θ : ℝ) (hM : 0 < M) (hr_ex : 2 * M < r) :
  Riemann M r θ Idx.θ Idx.φ Idx.θ Idx.φ = 2 * M * r * (Real.sin θ)^2 := by
  sorry -- Similar structure to R_trtr
```

**Priority:** CRITICAL (core of the solution)
**Difficulty:** MEDIUM (manageable algebra with component lemmas)
**Action:** Start with R_trtr as prototype, then adapt for others

---

## Phase 3: Refactor Ricci_zero_ext

**Current approach (c173658):**
```lean
theorem Ricci_zero_ext : ∀ (M r θ : ℝ), ... → Ricci M r θ μ ν = 0 := by
  -- Expand everything into monolithic expression
  unfold Ricci, Riemann, RiemannUp, ...
  -- Try to simplify (FAILS - too complex)
  ring
```

**New approach (modular):**
```lean
theorem Ricci_zero_ext : ∀ (M r θ : ℝ), ... → Ricci M r θ μ ν = 0 := by
  intro M r θ μ ν hM hr_ex h_sin_nz
  -- Ricci_{μν} = g^{ρσ} R_{ρμσν}
  unfold Ricci
  cases μ <;> cases ν

  case t.t =>
    -- R_tt = g^rr R_trtr + g^θθ R_tθtθ + g^φφ R_tφtφ
    simp only [sumIdx_expand, gInv]
    rw [Riemann_trtr_eq, Riemann_tθtθ_eq, Riemann_tφtφ_eq]
    -- Now just algebra with explicit values
    have hr_nz : r ≠ 0 := by linarith
    have hf_nz : f M r ≠ 0 := by sorry
    field_simp [hr_nz, hf_nz]
    ring

  case r.r =>
    -- R_rr = g^tt R_trtr + g^θθ R_rθrθ + g^φφ R_rφrφ
    simp only [sumIdx_expand, gInv]
    rw [Riemann_trtr_eq, Riemann_rθrθ_eq, Riemann_rφrφ_eq]
    -- Senior Professor's calculation:
    -- R_rr = 2M/(r³f) - M/(r³f) - M/(r³f) = 0
    have hr_nz : r ≠ 0 := by linarith
    have hf_nz : f M r ≠ 0 := by sorry
    field_simp [hr_nz, hf_nz]
    ring

  case θ.θ =>
    -- Similar pattern
    sorry

  case φ.φ =>
    -- Similar pattern
    sorry

  -- All off-diagonal cases are zero by symmetry
  all_goals sorry
```

**Priority:** CRITICAL
**Difficulty:** LOW (once component lemmas are proven)
**Action:** Implement after Phase 2 complete

---

## Phase 4: Infrastructure Fixes (Consult Junior Professor)

### Error 1: C∞ Differentiability
**Task:** Formalize smoothness argument for metric components
**Math (from Senior Professor):**
- Metric components are rational functions
- Domain: r > 2M, θ ∈ (0, π)
- Denominators are non-zero in domain
- Therefore C∞

**Junior Professor's task:**
- Find appropriate Mathlib theorems (DifferentiableAt, ContDiff, etc.)
- Structure the proof using exterior region hypotheses

### Error 2: Diagonal Metric Index Lowering
**Task:** Prove Γ_axb = g_aa · Γ^a_xb (no sum on a)
**Math (from Senior Professor):**
- Consequence of diagonal metric
- May need explicit lemma

**Junior Professor's task:**
- Resolve funext unification issue
- Potentially add intermediate lemma

### Error 3: Simp Made No Progress
**Task:** Identify and fix tactical issue
**Junior Professor's task:** Tactical debugging

---

## Implementation Priority

**Week 1: Core Mathematics**
1. ✅ Implement 3 algebraic helper lemmas (Phase 1)
2. ✅ Implement R_trtr component lemma as prototype (Phase 2.1)
3. ✅ Implement remaining 5 component lemmas (Phase 2.2-2.6)

**Week 2: Main Theorem**
4. ✅ Refactor Ricci_zero_ext using component lemmas (Phase 3)
5. ✅ Verify all 4 diagonal cases work
6. ✅ Handle off-diagonal cases (likely trivial)

**Week 3: Infrastructure**
7. ✅ Consult Junior Professor for C∞ proofs (Phase 4.1)
8. ✅ Fix remaining tactical issues (Phase 4.2-4.3)
9. ✅ Final verification: 0 sorrys, 0 errors

---

## Success Metrics

**After Phase 1:** 3 helper lemmas proven
**After Phase 2:** 6 component lemmas proven, Errors 4-7 should resolve
**After Phase 3:** Main theorem complete, 0 errors except infrastructure
**After Phase 4:** All 7 errors resolved, project complete

---

## Key Insights from Senior Professor

1. **Strategy Validation:** "The strategy attempted in f4e134f (using auxiliary lemmas) was the correct approach; it failed there only due to incorrect formulas."

2. **Divide and Conquer:** "The standard approach in General Relativity textbooks is modular computation (Divide and Conquer)."

3. **Manageable Algebra:** "This final calculation is a simple algebraic identity that ring can easily handle."

4. **Mathematics is Correct:** All infrastructure verified. Only tactical/structural issues remain.

---

**Generated:** October 5, 2025
**Status:** Ready to implement
**Next Action:** Begin Phase 1 (algebraic helper lemmas)
