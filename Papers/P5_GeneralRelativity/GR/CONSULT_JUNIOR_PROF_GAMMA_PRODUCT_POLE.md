# Consultation Request: Γ Product Indeterminate Form at Poles

**Date**: October 6, 2025
**Context**: Phase 2 Component Lemmas - R_θφθφ proof
**Issue**: Indeterminate form `0 · ∞` in Christoffel symbol product at θ = 0, π

---

## Problem Statement

Working on the final component lemma `Riemann_θφθφ_eq`:

```lean
lemma Riemann_θφθφ_eq (M r θ : ℝ) (hM : 0 < M) (hr_ex : 2 * M < r) :
    Riemann M r θ Idx.θ Idx.φ Idx.θ Idx.φ = 2 * M * r * Real.sin θ ^ 2
```

The proof requires computing the product `Γ_θ_φφ θ * Γ_φ_θφ θ`, where:

```lean
Γ_θ_φφ θ = -sin θ * cos θ
Γ_φ_θφ θ = cos θ / sin θ
```

---

## The Issue

### Off-Axis Case (sin θ ≠ 0)
**Works perfectly**:
```lean
Γ_θ_φφ θ * Γ_φ_θφ θ
  = (-sin θ * cos θ) * (cos θ / sin θ)
  = -cos² θ
```

This compiles with:
```lean
simp [Γ_θ_φφ, Γ_φ_θφ, div_mul_eq_mul_div]
field_simp [hsin]  -- hsin : sin θ ≠ 0
ring
```

### On-Axis Case (sin θ = 0)
**Indeterminate form `0 · ∞`**:
```
Γ_θ_φφ 0 = -sin 0 * cos 0 = 0
Γ_φ_θφ 0 = cos 0 / sin 0 = ±1 / 0 = ±∞
```

Product: `0 · ∞` is indeterminate

---

## Current Proof Attempt

```lean
have hprod : Γ_θ_φφ θ * Γ_φ_θφ θ = -(Real.cos θ) ^ 2 := by
  by_cases hsin : Real.sin θ = 0
  · -- On-axis: Need to prove 0 · ∞ = -cos² θ
    simp [Γ_θ_φφ, hsin, mul_zero]
    -- Goal: 0 = -cos² θ
    -- But cos² 0 = 1, so this is 0 = -1 (FALSE!)
    sorry
  · -- Off-axis: proven above
    simp [Γ_θ_φφ, Γ_φ_θφ, div_mul_eq_mul_div]
    field_simp [hsin]
    ring
```

**Error**: After `simp [Γ_θ_φφ, hsin, mul_zero]`, the goal becomes `0 = -cos² θ`, which is false when θ = 0 (since cos 0 = 1).

---

## Mathematical Analysis

### Why Does This Product Appear?

In the Riemann tensor computation:
```
R_θφθφ = ... - Γ^θ_rθ · Γ^r_φφ - Γ^θ_φφ · Γ^φ_θφ + ...
```

The term `-Γ^θ_φφ · Γ^φ_θφ` involves this problematic product.

### Physical Context

At the poles (θ = 0, π):
- The coordinate system is singular
- The φ coordinate becomes undefined
- Christoffel symbols with φ indices may diverge
- BUT the Riemann tensor must be well-defined (it's a tensor!)

### Expected Behavior

Since `R_θφθφ = 2Mr·sin² θ`, when sin θ = 0:
```
R_θφθφ = 2Mr · 0 = 0
```

So the LHS (which contains the problematic product) must also equal 0.

---

## Questions for Junior Professor

1. **Limit Interpretation**: Should we compute:
   ```
   lim_{θ → 0} [Γ_θ_φφ θ * Γ_φ_θφ θ]
   ```
   using L'Hôpital or trigonometric identities?

2. **Well-Definedness**: Is the product `Γ_θ_φφ · Γ_φ_θφ` actually well-defined at θ = 0 in the context of the full Riemann tensor formula? Perhaps cancellations occur before evaluating individual Γ symbols?

3. **Alternative Approach**: Should we:
   - Avoid expanding Γ_φ_θφ when sin θ = 0?
   - Prove the entire expression equals 0 without isolating the product?
   - Use a different coordinate representation near poles?

4. **Lean Tactic**: What's the right way to prove:
   ```lean
   lim_{θ → 0} [(-sin θ · cos θ) · (cos θ / sin θ)] = -1
   ```
   in Lean 4?

---

## Attempted Solutions

### Attempt 1: Separate Cases
```lean
by_cases hsin : Real.sin θ = 0
· simp only [hsin, pow_two, mul_zero, zero_mul]
  -- Goal becomes: r = 0 ∨ cos θ = 0
  -- Both are FALSE in our context!
```

### Attempt 2: Compute Product Directly
```lean
simp [Γ_θ_φφ, hsin, mul_zero]
-- Goal: 0 = -cos² θ
-- This is false when θ = 0
```

### Attempt 3: Avoid Case Split
```lean
-- Prove hprod for all θ without cases
simp [Γ_θ_φφ, Γ_φ_θφ, div_mul_eq_mul_div]
field_simp  -- FAILS: needs sin θ ≠ 0 hypothesis
```

---

## Impact

**Status**: 5/6 component lemmas proven
**Blocker**: This single on-axis case for R_θφθφ

Once resolved:
- ✅ All 6 Riemann component lemmas complete
- ✅ Phase 2 complete
- → Proceed to Phase 3: Refactor diagonal Ricci cases using component lemmas

---

## Minimal Reproducible Example

```lean
lemma gamma_product_at_pole (θ : ℝ) (hsin : Real.sin θ = 0) :
    (-Real.sin θ * Real.cos θ) * (Real.cos θ / Real.sin θ) = -(Real.cos θ) ^ 2 := by
  sorry  -- How to prove this when sin θ = 0?
```

**Question**: How do we handle the `0 · ∞` indeterminate form here?

---

## Request

Please advise on:
1. The mathematically correct interpretation of this product at θ = 0
2. The appropriate Lean 4 tactics/lemmas to prove it
3. Whether we should restructure the proof to avoid this issue entirely

Thank you for your guidance!
