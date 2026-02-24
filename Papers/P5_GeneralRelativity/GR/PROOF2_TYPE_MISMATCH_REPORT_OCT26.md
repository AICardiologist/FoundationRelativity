# Proof #2 Type Mismatch - Diagnostic Report

**Date**: October 26, 2025
**Agent**: Claude Code (Sonnet 4.5)
**Status**: ❌ **BLOCKED - Mathematical Mismatch Between Lemmas**

---

## TL;DR

JP's 3-step proof approach fails because `sum_k_prod_rule_to_Γ₁` gives **only ∂Γ₁ terms**, while `Riemann_via_Γ₁` shows `Riemann = ∂Γ₁ + [Γ·Γ terms]`.

**The gap**: We're claiming `∂Γ₁ = Riemann`, but actually `Riemann = ∂Γ₁ + [Γ·Γ terms]`.

This requires either:
1. The Γ·Γ terms somehow appear in the LHS expansion (via metric derivative terms), OR
2. The lemma statement is mathematically incorrect, OR
3. There's a hidden cancellation we're not seeing

---

## What We're Trying to Prove

**Lemma**: `regroup_right_sum_to_Riemann_CORRECT` (lines 11043-11063)

**Statement**:
```lean
∑_k [∂_r(Γtot^k_{θa} · g_{kb}) - ∂_θ(Γtot^k_{ra} · g_{kb})]
  = Riemann M r θ b a Idx.r Idx.θ
```

---

## The 3-Step Proof Attempt

### Step 1: Apply `sum_k_prod_rule_to_Γ₁` ✅ WORKS

```lean
∑_k [∂_r(Γtot^k_{θa} · g_{kb}) - ∂_θ(Γtot^k_{ra} · g_{kb})]
  = ∂_r Γ₁_{baθ} - ∂_θ Γ₁_{bar}
```

**Status**: ✅ This step compiles, proven by Proof #1

**What it gives**: Just the **derivative of Γ₁** terms, no Γ·Γ

---

### Step 2: Apply `Riemann_via_Γ₁.symm` ❌ TYPE MISMATCH

**What we have**:
```lean
∂_r Γ₁_{baθ} - ∂_θ Γ₁_{bar}
```

**What we want to show**:
```lean
= sumIdx (fun ρ => RiemannUp M r θ ρ a Idx.r Idx.θ * g M ρ b r θ)
```

**What `Riemann_via_Γ₁` actually states** (lines 2516-2524):
```lean
Riemann M r θ β a Idx.r Idx.θ
  = ∂_r Γ₁_{βaθ} - ∂_θ Γ₁_{βar}
    + sumIdx (fun lam =>
        Γ₁ M r θ lam a Idx.r * Γtot M r θ lam β Idx.θ
      - Γ₁ M r θ lam a Idx.θ * Γtot M r θ lam β Idx.r)
```

**The Problem**: When we `.symm` this for `β = b`, we get:
```lean
∂_r Γ₁_{baθ} - ∂_θ Γ₁_{bar} + [Γ·Γ terms]
  = Riemann M r θ b a Idx.r Idx.θ
```

But we have **only** `∂_r Γ₁_{baθ} - ∂_θ Γ₁_{bar}` (no Γ·Γ terms)!

---

## The Type Mismatch Error

```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:11060:12: Type mismatch

After simplification, term Eq.symm (Riemann_via_Γ₁ M r θ h_ext h_θ b a) has type:

  ((deriv (fun s => Γ₁ M s θ b a Idx.θ) r
  - deriv (fun t => Γ₁ M r t b a Idx.r) θ
  - sumIdx fun i => Γtot M r θ i b Idx.r * Γ₁ M r θ i a Idx.θ)
  + sumIdx fun i => Γtot M r θ i b Idx.θ * Γ₁ M r θ i a Idx.r)
    = RiemannUp M r θ b a Idx.r Idx.θ * g_{bb}

but is expected to have type:

  deriv (fun s => Γ₁ M s θ b a Idx.θ) r
  - deriv (fun t => Γ₁ M r t b a Idx.r) θ
    = sumIdx fun ρ => RiemannUp M r θ ρ a Idx.r Idx.θ * g_{ρb}
```

**Analysis**:

**What Lean computed from `Riemann_via_Γ₁.symm`**:
- LHS: `(∂Γ₁ - ∂Γ₁ - Γ·Γ) + Γ·Γ` = `∂Γ₁ - ∂Γ₁ + [Γ·Γ combination]`
- RHS: `RiemannUp * g_{bb}` (simplified to diagonal)

**What we need**:
- LHS: Just `∂Γ₁ - ∂Γ₁` (no Γ·Γ terms)
- RHS: `sumIdx (RiemannUp * g)` (not simplified)

**The mismatch**: We have `∂Γ₁` on LHS, but `Riemann_via_Γ₁` adds Γ·Γ terms!

---

## Mathematical Analysis

### What Does the LHS Actually Compute?

```lean
∑_k [∂_r(Γtot^k_{θa} · g_{kb}) - ∂_θ(Γtot^k_{ra} · g_{kb})]
```

Expanding with product rule:
```
= ∑_k [(∂_r Γtot^k_{θa}) · g_{kb} + Γtot^k_{θa} · (∂_r g_{kb})]
  - ∑_k [(∂_θ Γtot^k_{ra}) · g_{kb} + Γtot^k_{ra} · (∂_θ g_{kb})]

= ∑_k [(∂_r Γtot^k_{θa} - ∂_θ Γtot^k_{ra}) · g_{kb}]
  + ∑_k [Γtot^k_{θa} · (∂_r g_{kb}) - Γtot^k_{ra} · (∂_θ g_{kb})]
```

**First term**:
```
∑_k [(∂_r Γtot^k_{θa} - ∂_θ Γtot^k_{ra}) · g_{kb}]
```
This is the contraction of the "kinematic" part of RiemannUp.

**Second term**:
```
∑_k [Γtot^k_{θa} · (∂_r g_{kb}) - Γtot^k_{ra} · (∂_θ g_{kb})]
```
This involves **metric derivatives**.

### Key Question: What Are the Metric Derivative Terms?

In a metric-compatible connection (∇g = 0):
```
∂_μ g_{ab} = Γ^λ_{μa} g_{λb} + Γ^λ_{μb} g_{λa}
```

So:
```
∑_k Γtot^k_{θa} · (∂_r g_{kb})
  = ∑_k Γtot^k_{θa} · (Γ^λ_{r k} g_{λb} + Γ^λ_{r b} g_{λk})
```

**Hypothesis**: Maybe these metric derivative terms combine with the kinematic terms to give the full Riemann (including Γ·Γ)?

**Problem**: This doesn't match the structure of `sum_k_prod_rule_to_Γ₁`, which claims:
```
∑_k [∂_r(Γtot·g) - ∂_θ(Γtot·g)] = ∂_r Γ₁ - ∂_θ Γ₁
```

If this is true, then the product rule expansion **must** simplify to just ∂Γ₁, meaning:
```
∑_k [Γtot^k_{θa} · (∂_r g_{kb}) - Γtot^k_{ra} · (∂_θ g_{kb})] = 0   ???
```

But this seems wrong! Metric derivatives don't vanish in general.

---

## Possible Resolutions

### Option 1: Metric Derivative Terms Create Γ·Γ

**Hypothesis**: The metric derivative terms in the product rule expansion are exactly the Γ·Γ terms needed.

**Check**: Does `sum_k_prod_rule_to_Γ₁` actually prove:
```
∑_k [∂_r(Γtot·g) - ∂_θ(Γtot·g)] = ∂_r Γ₁ - ∂_θ Γ₁
```

Or does it prove something weaker?

**Action**: Read the actual proof of `sum_k_prod_rule_to_Γ₁` (lines 10942-11034) to see if it handles metric derivatives.

---

### Option 2: The Lemma Statement Is Wrong

**Hypothesis**: The lemma `regroup_right_sum_to_Riemann_CORRECT` is mathematically incorrect.

**Evidence**:
- We're claiming LHS = Riemann
- But Riemann = ∂Γ₁ + [Γ·Γ]
- And LHS = ∂Γ₁ (according to `sum_k_prod_rule_to_Γ₁`)
- So we'd need Γ·Γ = 0, which is false for Schwarzschild

**Countercheck**: Are there deleted lemmas that were proven false?

Yes! Lines 11065-11082 mention:
```
Previously this section contained two lemmas that attempted to prove
pointwise identities that don't hold:
  * regroup_right_sum_to_RiemannUp_NEW
  * regroup_left_sum_to_RiemannUp_NEW

Counterexample (flat 2D polar coordinates):
  Setting: Flat Euclidean space in polar coordinates
  Result: LHS = 1, RHS = 0 → lemmas are false
```

**Concern**: Is `regroup_right_sum_to_Riemann_CORRECT` also false?

---

### Option 3: Hidden Cancellation in Schwarzschild Metric

**Hypothesis**: For the specific case of Schwarzschild metric, some special structure makes Γ·Γ terms cancel.

**Check**: Does the Schwarzschild metric have special properties (spherical symmetry, diagonal metric) that make this work?

**Problem**: Even if true, the lemma is stated generally for all M, r, θ in Exterior domain, not just Schwarzschild.

---

### Option 4: Misunderstanding of `sum_k_prod_rule_to_Γ₁`

**Hypothesis**: Maybe `sum_k_prod_rule_to_Γ₁` doesn't just give `∂Γ₁`, but actually includes hidden Γ·Γ terms via the metric derivatives?

**Action**: Read the actual statement and proof of `sum_k_prod_rule_to_Γ₁` more carefully.

---

## Request for JP

**Questions**:

1. **Does `sum_k_prod_rule_to_Γ₁` really give just `∂Γ₁`?**
   - Or does it give `∂Γ₁ + [metric derivative terms]`?
   - Can you clarify what the RHS of Proof #1 actually is?

2. **How do the Γ·Γ terms appear in the proof?**
   - `Riemann_via_Γ₁` clearly has Γ·Γ terms
   - But Step 1 gives only ∂Γ₁
   - Where do the Γ·Γ terms come from?

3. **Is the lemma statement correct?**
   - Does `∑_k [∂_r(Γ·g) - ∂_θ(Γ·g)] = Riemann` hold mathematically?
   - Or should the RHS be something else (e.g., just the kinematic part)?

4. **Alternative approach?**
   - Should we use a different lemma instead of `Riemann_via_Γ₁`?
   - Is there a version that separates kinematic and Γ·Γ parts?

---

## Build Error Summary

**File**: `Riemann.lean`
**Lines**: 11060 (Step 2), 11063 (Step 3)
**Exit Code**: 1 (compilation failed)

**Errors**:
1. Line 11060: Type mismatch when applying `Riemann_via_Γ₁.symm`
   - LHS has Γ·Γ terms, expected type doesn't
2. Line 11063: Type mismatch in final step (consequence of error 1)

**Root Cause**: Mathematical mismatch between what Step 1 gives and what Step 2 expects

---

## Current Status

**Proof #1**: ✅ Complete and verified
**Proof #2**: ❌ Blocked on mathematical gap

**Next Steps**:
1. Send this report to JP for clarification
2. Await mathematical guidance on resolving the Γ·Γ term mismatch
3. Consider alternative proof strategies if current approach is fundamentally flawed

---

**Prepared By**: Claude Code (Sonnet 4.5)
**Date**: October 26, 2025
**Status**: ❌ **Blocked - Awaiting JP Clarification on Γ·Γ Terms**

---
