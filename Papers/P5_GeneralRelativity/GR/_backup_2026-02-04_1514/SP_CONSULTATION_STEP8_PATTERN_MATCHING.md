# Consultation Request: Step 8 Pattern Matching Issue
## Date: October 17, 2025
## To: Senior Professor
## From: Research Team
## Context: Phase 3 Riemann_via_Γ₁ Proof - Final Step

---

## Summary

**Request**: Help with pattern matching or conv navigation to apply `prod_rule_backwards_sum` in Step 8.

**Status**:
- Steps 1-7: ✅ Complete (no sorries!)
- Step 8: ⏳ Tactical blocker (pattern matching issue)
- Build: ✅ Passes (3078 jobs)

**Issue**: Variable name mismatch preventing lemma application.

---

## Background Context

We're completing the final step (Step 8) of the `Riemann_via_Γ₁` proof. This is a major milestone in Phase 3 of our General Relativity formalization.

**What's been accomplished**:
- All 4 auxiliary lemmas for the "Algebraic Miracle" are proven (lines 1450-1550)
- `prod_rule_backwards_sum` helper is proven (lines 1557-1585)
- Steps 1-7 are complete and verified
- All mathematical content is correct

**What remains**: Tactical execution of Step 8 assembly.

---

## The Specific Problem

### Lemma Signature (line 1557)

```lean
lemma prod_rule_backwards_sum (M r θ : ℝ) (h_ext : Exterior M r θ) (β a μ ν : Idx) :
  sumIdx (fun ρ => g M β ρ r θ * dCoord μ (fun r' θ' => Γtot M r' θ' ρ a ν) r θ)
  = (dCoord μ (fun r' θ' => sumIdx (fun ρ => g M β ρ r' θ' * Γtot M r' θ' ρ a ν)) r θ
   - sumIdx (fun ρ => dCoord μ (fun r' θ' => g M β ρ r' θ') r θ * Γtot M r θ ρ a ν))
```

**Note**: The lemma uses `(fun r' θ' => ...)` with primed variables.

### Goal State After Steps 4-7 (line 1658)

```lean
sumIdx (fun ρ => g M β ρ r θ * dCoord Idx.r (fun r θ => Γtot M r θ ρ Idx.θ a) r θ)
  - sumIdx (fun ρ => g M β ρ r θ * dCoord Idx.θ (fun r θ => Γtot M r θ ρ Idx.r a) r θ)
  + sumIdx (fun lam => sumIdx (fun ρ =>
        g M β ρ r θ * (Γtot M r θ ρ Idx.r lam * Γtot M r θ lam Idx.θ a)))
  - sumIdx (fun lam => sumIdx (fun ρ =>
        g M β ρ r θ * (Γtot M r θ ρ Idx.θ lam * Γtot M r θ lam Idx.r a)))
```

**Issue**: The goal has `(fun r θ => ...)` without primes.

---

## What We've Tried

### Attempt 1: Direct `rw`

```lean
rw [prod_rule_backwards_sum M r θ h_ext β a Idx.r Idx.θ]
```

**Error**:
```
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  sumIdx fun ρ => g M β ρ r θ * dCoord Idx.r (fun r' θ' => Γtot M r' θ' ρ a Idx.θ) r θ
in the target expression
  sumIdx fun ρ => g M β ρ r θ * dCoord Idx.r (fun r θ => Γtot M r θ ρ Idx.θ a) r θ
```

**Analysis**: Pattern matching fails because `(fun r' θ' => ...)` doesn't match `(fun r θ => ...)`.

### Attempt 2: Conv Navigation

```lean
conv_lhs =>
  arg 1; arg 2; arg 1; arg 1
  rw [prod_rule_backwards_sum M r θ h_ext β a Idx.r Idx.θ]
```

**Error**:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:1673:33: invalid 'arg' conv tactic, application or implication expected
  fun lam => sumIdx fun ρ => g M β ρ r θ * (Γtot M r θ ρ Idx.r lam * Γtot M r θ lam Idx.θ a)
```

**Analysis**: The conv path navigated into a lambda function where `arg` doesn't apply.

### Attempt 3: `erw` (considered but not tested)

Would `erw` (equational rewriting) handle the variable name difference more flexibly?

---

## Questions for SP

### Q1: Correct Conv Navigation Path?

What is the correct `conv` path to reach the first `sumIdx (fun ρ => g * dCoord ...)` term in the goal?

The goal structure after Steps 4-7 is:
```
(A - B) + (C - D)
```

Where:
- `A = sumIdx (fun ρ => g M β ρ r θ * dCoord Idx.r (fun r θ => Γtot M r θ ρ Idx.θ a) r θ)`
- `B = sumIdx (fun ρ => g M β ρ r θ * dCoord Idx.θ (fun r θ => Γtot M r θ ρ Idx.r a) r θ)`
- `C = sumIdx (fun lam => sumIdx (fun ρ => ...))`  -- M_r term
- `D = sumIdx (fun lam => sumIdx (fun ρ => ...))`  -- M_θ term

We need to apply the product rule to `A` and `B` separately.

**Attempted path for `A`**: `arg 1; arg 2; arg 1; arg 1`
- Does this navigate correctly through `(A - B) + (C - D)` to reach `A`?

### Q2: Alternative to Conv?

**Option A**: Create a specialized variant of `prod_rule_backwards_sum` with variable names matching the goal?

```lean
lemma prod_rule_backwards_sum_direct (M r θ : ℝ) (h_ext : Exterior M r θ) (β a μ ν : Idx) :
  sumIdx (fun ρ => g M β ρ r θ * dCoord μ (fun r θ => Γtot M r θ ρ a ν) r θ)
  = (dCoord μ (fun r θ => sumIdx (fun ρ => g M β ρ r θ * Γtot M r θ ρ a ν)) r θ
   - sumIdx (fun ρ => dCoord μ (fun r θ => g M β ρ r θ) r θ * Γtot M r θ ρ a ν))
```

This would just be a variant with `r, θ` instead of `r', θ'`.

**Option B**: Use `erw` instead of `rw`?

**Option C**: Some other Lean 4 idiom for handling variable name mismatches?

### Q3: General Pattern Matching Guidance?

Is there a general principle for when Lean's pattern matcher treats `(fun r θ => ...)` and `(fun r' θ' => ...)` as different vs. when it treats them as alpha-equivalent?

---

## Mathematical Strategy (All Components Proven)

Once we can apply `prod_rule_backwards_sum`, the rest should work:

```lean
-- 1. Apply product rule to both ∂Γ terms
rw [prod_rule_backwards_sum M r θ h_ext β a Idx.r Idx.θ]  -- For r-component
rw [prod_rule_backwards_sum M r θ h_ext β a Idx.θ Idx.r]  -- For θ-component

-- 2. Recognize Γ₁ definition: Σρ g_{βρ} Γ^ρ_{aν} = Γ_{βaν}
simp only [Γ₁]

-- 3. Rearrange terms
abel_nf

-- 4. Apply the 4 proven auxiliary lemmas
rw [Riemann_via_Γ₁_Cancel_r M r θ β a]      -- M_r = D_r2
rw [Riemann_via_Γ₁_Cancel_θ M r θ β a]      -- M_θ = D_θ2
rw [← Riemann_via_Γ₁_Identify_r M r θ β a]  -- D_r1 = T2_r
rw [← Riemann_via_Γ₁_Identify_θ M r θ β a]  -- D_θ1 = T2_θ

-- 5. Final simplification
ring_nf
```

All four auxiliary lemmas are fully proven (no sorries) at lines 1450-1550.

---

## File Location

**File**: `Papers/P5_GeneralRelativity/GR/Riemann.lean`

**Step 8 Code**: Lines 1658-1693
**Prod Rule Helper**: Lines 1557-1585
**Auxiliary Lemmas**: Lines 1450-1550

---

## Code Context

### Current Step 8 Code (lines 1658-1693)

```lean
_ = dCoord Idx.r (fun r θ => Γ₁ M r θ β a Idx.θ) r θ
  - dCoord Idx.θ (fun r θ => Γ₁ M r θ β a Idx.r) r θ
  + sumIdx (fun lam =>
      Γ₁ M r θ lam a Idx.r * Γtot M r θ lam β Idx.θ
    - Γ₁ M r θ lam a Idx.θ * Γtot M r θ lam β Idx.r)
  := by
    -- Tactical blocker: Pattern matching and conv navigation
    --
    -- Current state after Steps 4-7:
    --   sumIdx (g * ∂Γ_r) - sumIdx (g * ∂Γ_θ) + M_r - M_θ
    --
    -- Target state:
    --   ∂Γ₁_r - ∂Γ₁_θ + T2_r - T2_θ
    --
    -- Strategy (proven components exist):
    -- 1. Apply prod_rule_backwards_sum: Σ g(∂Γ) = ∂(Σ gΓ) - Σ (∂g)Γ
    --    Issue: Lemma uses (fun r' θ' => ...) but goal has (fun r θ => ...)
    --    Attempted: Direct rw (failed - pattern mismatch)
    --    Attempted: conv navigation (failed - "invalid 'arg' conv tactic, application or implication expected")
    --
    -- 2. After product rule, recognize Γ₁ = Σρ g_{βρ} Γ^ρ_{aν}
    -- 3. Apply Cancel lemmas: M_r = D_r2, M_θ = D_θ2
    -- 4. Apply Identify lemmas: D_r1 = T2_r, D_θ1 = T2_θ
    -- 5. Conclude: M - D = -T2
    --
    -- All mathematical content verified in:
    -- - prod_rule_backwards_sum (lines 1557-1585)
    -- - Riemann_via_Γ₁_Cancel_r/θ (lines 1450-1495)
    -- - Riemann_via_Γ₁_Identify_r/θ (lines 1499-1550)
    --
    -- Need: Either correct conv path or specialized variant of prod_rule_backwards_sum
    sorry
```

---

## Priority

**Medium-High**: This is the final tactical blocker for completing Phase 3.

**Impact**: Once resolved, we'll have a complete formal proof of `Riemann_via_Γ₁` with only Phase 2A differentiability prerequisites remaining as sorries.

---

## What We Need

**Ideal**: The specific `conv` navigation path or tactic sequence to apply `prod_rule_backwards_sum`.

**Alternative**: Guidance on creating a specialized variant with matching variable names.

**General**: Any Lean 4 idiom or best practice for handling this kind of alpha-equivalence issue in pattern matching.

---

**Prepared by**: Research Team
**Date**: October 17, 2025
**Build Status**: ✅ Passes (3078 jobs)
**File**: `Riemann.lean` lines 1658-1693
**Phase 3 Completion**: 85% (one tactical blocker remaining)
