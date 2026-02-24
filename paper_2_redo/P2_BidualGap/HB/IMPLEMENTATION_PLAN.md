# Implementation Plan for Dual Isometries (Based on Math Team Guidance)

## Overview
Complete the dual isometry proofs to discharge the two placeholder axioms in the WLPO ↔ BidualGapStrong theorem.

## Key Mathematical Insights from Professor

### 1. DualIsBanach Structure (Revised)
Replace the placeholder with:
```lean
structure DualIsBanach (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop where
  -- Located/approximable operator norm
  (norm_located : ∀ f : X →L[ℝ] ℝ, ∀ ε > 0, ∃ q : ℚ≥0, |‖f‖ - q| ≤ ε)
  (norm_attained : ∀ f : X →L[ℝ] ℝ, ∀ ε > 0, ∃ x : X, ‖x‖ ≤ 1 ∧ ‖f x‖ ≥ ‖f‖ - ε)
  -- Metric completeness
  (complete : CompleteSpace (X →L[ℝ] ℝ))
  -- Algebraic closure (easy corollaries)
  (closed_zero : HasOperatorNorm (0 : X →L[ℝ] ℝ))
  (closed_neg : ∀ f, HasOperatorNorm f → HasOperatorNorm (-f))
  (closed_smul : ∀ (a : ℝ) f, HasOperatorNorm f → HasOperatorNorm (a • f))
  (closed_add : ∀ f g, HasOperatorNorm f → HasOperatorNorm g → HasOperatorNorm (f + g))
```

### 2. The σ_ε Trick (Key Innovation)
Instead of using sign functions (which require decidability), use:
```lean
def sigma_eps (ε : ℝ) (t : ℝ) : ℝ := t / (|t| + ε)
```
Properties:
- Always in [-1, 1]
- Continuous and constructive
- σ_ε(0) = 0
- For t ≠ 0: σ_ε(t) ≈ sign(t) as ε → 0

### 3. Where WLPO is Used
- **NOT** for the isometries themselves
- **NOT** for completeness proofs
- **ONLY** for locating suprema in ℓ^∞: Given b : ℕ → ℝ bounded, WLPO lets us approximate sup_n |b_n|

## Implementation Steps

### Phase 1: Core Isometry (c₀ →L[ℝ] ℝ) ≃ₗᵢ ℓ¹

#### Step 1.1: Forward Map (toCoeffs)
```lean
def toCoeffs : (c₀ →L[ℝ] ℝ) →ₗ[ℝ] (ℕ → ℝ) where
  toFun f := fun n => f (e n)
  map_add' := -- straightforward
  map_smul' := -- straightforward
```

#### Step 1.2: Summability Proof
```lean
lemma toCoeffs_summable (f : c₀ →L[ℝ] ℝ) : Summable (fun n => ‖f (e n)‖) := by
  -- Use signVector from DirectDual.lean:
  -- For any finite F ⊆ ℕ, ∑_{n∈F} |f(e_n)| ≤ ‖f‖
  -- Hence partial sums bounded → summable
```

#### Step 1.3: Norm Equality (Upper Bound)
```lean
lemma toCoeffs_norm_le (f : c₀ →L[ℝ] ℝ) : ∑' n, ‖f (e n)‖ ≤ ‖f‖ := by
  -- Direct from signVector bounds on finite sets
```

#### Step 1.4: Norm Equality (Lower Bound) - Using σ_ε
```lean
lemma toCoeffs_norm_ge (f : c₀ →L[ℝ] ℝ) : ‖f‖ ≤ ∑' n, ‖f (e n)‖ := by
  intro ε
  -- Pick finite F with tail sum < ε/2
  -- Define x_F^ε = ∑_{n∈F} σ_ε(f(e_n)) · e_n
  -- Show f(x_F^ε) ≥ ∑_{n∈F} |f(e_n)| - ε|F|
  -- Hence ‖f‖ ≥ ∑ |f(e_n)| - ε
```

#### Step 1.5: Inverse Map (ofCoeffs)
```lean
def ofCoeffs : ℓ¹ →ₗ[ℝ] (c₀ →L[ℝ] ℝ) where
  toFun a := {
    toFun := fun x => ∑' n, a n * x n
    cont := -- absolute convergence from ℓ¹ × c₀
  }
  map_add' := -- termwise
  map_smul' := -- termwise
```

#### Step 1.6: Bundle as LinearIsometryEquiv
```lean
def dual_c0_iso_l1 : (c₀ →L[ℝ] ℝ) ≃ₗᵢ ℓ¹ := {
  toLinearEquiv := -- combine toCoeffs and ofCoeffs
  norm_map' := -- use norm equality lemmas
}
```

### Phase 2: Second Isometry (ℓ¹ →L[ℝ] ℝ) ≃ₗᵢ ℓ^∞

Similar pattern:
1. Extract coefficients φ ↦ (φ(e₀), φ(e₁), ...)
2. Show boundedness (coefficients in ℓ^∞)
3. Norm equality via σ_ε on finite sets
4. Inverse: b ↦ (x ↦ ∑ x_n b_n)
5. Bundle as LinearIsometryEquiv

### Phase 3: Transport Lemma

```lean
lemma DualIsBanach.congr {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] (e : X ≃ₗᵢ Y) :
  DualIsBanach X ↔ DualIsBanach Y := by
  -- Define pullback on duals
  -- Show norm preservation
  -- Transport completeness
```

### Phase 4: WLPO → Locatedness

```lean
lemma located_sup_norm_of_WLPO (h : WLPO) (b : ℕ → ℝ) 
  (hb : BddAbove (Set.range (fun n => |b n|))) :
  ∀ ε > 0, ∃ q : ℚ≥0, |sSup (Set.range (fun n => |b n|)) - q| ≤ ε := by
  -- Binary search using WLPO on "∃n, |b_n| > q"
  -- Bisect rational interval containing supremum
```

### Phase 5: Final Discharge

```lean
theorem dual_is_banach_c0_from_WLPO (h : WLPO) : DualIsBanach c₀ := by
  -- Transport from ℓ¹ using dual_c0_iso_l1
  -- ℓ¹ has DualIsBanach constructively (finite sums locate norm)
  
theorem dual_is_banach_c0_dual_from_WLPO (h : WLPO) :
  DualIsBanach (c₀ →L[ℝ] ℝ) := by
  -- Chain: (c₀ →L ℝ) ≃ₗᵢ ℓ¹
  -- Then: (ℓ¹ →L ℝ) ≃ₗᵢ ℓ^∞
  -- Use WLPO for locatedness on ℓ^∞
```

## Technical Notes

### Mathlib Types to Use
- `c₀`: Already exists as `ZeroAtInfty` 
- `ℓ¹`: Use `lp (fun _ : ℕ => ℝ) 1`
- `ℓ^∞`: Use `lp (fun _ : ℕ => ℝ) ⊤` or `ℕ →ᵇ ℝ` (bounded functions)

### Key Lemmas from Mathlib
- `hasSum_mul_right`, `summable.mul_right`
- `summable_of_nonneg_of_le` (for bounds)
- `norm_tsum_le` variants
- `ContinuousLinearMap.compL` for composition

### Testing Strategy
1. First implement σ_ε and verify its properties
2. Test toCoeffs on simple functionals (e.g., coordinate projections)
3. Verify norm preservation on concrete examples
4. Check that composition toCoeffs ∘ ofCoeffs = id

## Success Criteria
- [ ] All 27 sorries in DualIsometries.lean resolved
- [ ] `#print axioms` shows no project-level axioms
- [ ] Regression tests pass
- [ ] Paper v4 can claim "axiom-free" for main theorem

## Timeline Estimate
- Phase 1: 2-3 days (most complex, establishing patterns)
- Phase 2: 1 day (similar to Phase 1)
- Phase 3: 1 day (transport infrastructure)
- Phase 4: 1 day (WLPO bisection)
- Phase 5: 1 day (putting it together)
- Testing/Polish: 2 days

Total: ~1 week of focused implementation