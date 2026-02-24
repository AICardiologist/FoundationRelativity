# Blocker on Left Regrouping Implementation
## Date: October 18, 2025
## Issue: Goal shape mismatch after compatibility expansion

---

## Summary

Attempted to implement `regroup_left_sum_to_RiemannUp` using your mirror f₁...f₈ definitions, but encountered a goal shape mismatch. The issue occurs at step ③ where we try to apply H₁ and H₂ to contract the Γ-Γ terms.

---

## What I Did

Following your guidance, I:

1. ✅ Used your exact mirror f₁...f₈ definitions
2. ✅ Defined the mixed-left collector call
3. ❌ Hit pattern mismatch when trying to `rw [H₁, H₂, h_collect]`

---

## The Blocker

### Goal state after `simp_rw [compat_r_a_e, compat_θ_a_e]` and distribution:

```lean
(sumIdx fun k =>
    dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ b) r θ * g M a k r θ +
          -(dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r b) r θ * g M a k r θ) +
        ((Γtot M r θ k Idx.θ b * sumIdx fun k_1 => Γtot M r θ k_1 Idx.r a * g M k_1 k r θ) +
          Γtot M r θ k Idx.θ b * sumIdx fun k_1 => Γtot M r θ k_1 Idx.r k * g M a k_1 r θ) +
      -((Γtot M r θ k Idx.r b * sumIdx fun k_1 => Γtot M r θ k_1 Idx.θ a * g M k_1 k r θ) +
          Γtot M r θ k Idx.r b * sumIdx fun k_1 => Γtot M r θ k_1 Idx.θ k * g M a k_1 r θ)) =
  g M a a r θ * RiemannUp M r θ a b Idx.r Idx.θ
```

### Key observation:

The compatibility expansion creates **two** Γ-Γ terms for each:
1. `Γ k_1 · a * g_{k_1 k}` (contracts to index `a` via diagonal)
2. `Γ k_1 · k * g_{a k_1}` (this is what H₁/H₂ handle)

### What H₁ expects to rewrite:

```lean
sumIdx (fun k => Γtot M r θ k Idx.θ b *
                   sumIdx (fun lam => Γtot M r θ lam Idx.r k * g M a lam r θ))
```

### What's actually in the goal:

```lean
Γtot M r θ k Idx.θ b * sumIdx fun k_1 => Γtot M r θ k_1 Idx.r a * g M k_1 k r θ  -- Extra term!
+ Γtot M r θ k Idx.θ b * sumIdx fun k_1 => Γtot M r θ k_1 Idx.r k * g M a k_1 r θ  -- What H₁ expects
```

The goal has BOTH terms, but H₁ only knows how to handle the second one.

---

## What H₁ and H₂ Do

### H₁ (lines 4070-4080):
```lean
have H₁ :
  sumIdx (fun k => Γtot M r θ k Idx.θ b *
                     sumIdx (fun lam => Γtot M r θ lam Idx.r k * g M a lam r θ))
    =
  sumIdx (fun k => g M a k r θ *
                     sumIdx (fun lam => Γtot M r θ k Idx.r lam * Γtot M r θ lam Idx.θ b)) := by
  classical
  simp only [sumIdx_expand]
  simp only [g, sumIdx_mul_g_left]  -- This contracts the diagonal
  ring
```

**Purpose**: Contract `Γ lam · k * g_{a lam}` to `g_{a k}` via diagonal, then reassociate

### H₂ (lines 4082-4093):
```lean
have H₂ :
  sumIdx (fun k => Γtot M r θ k Idx.r b *
                     sumIdx (fun lam => Γtot M r θ lam Idx.θ k * g M a lam r θ))
    =
  sumIdx (fun k => g M a k r θ *
                     sumIdx (fun lam => Γtot M r θ k Idx.θ lam * Γtot M r θ lam Idx.r b)) := by
  classical
  simp only [sumIdx_expand]
  simp only [g, sumIdx_mul_g_left]
  ring
```

**Purpose**: Mirror of H₁ for the other Γ-Γ pair

---

## The Question

After the compatibility expansion, we have:
- **4 original ∂Γ terms** (already in the right shape)
- **4 Γ·∂g terms** (from the second part of compatibility)
- **4 extra Γ-Γ terms** involving `Γ k_1 · a * g_{k_1 k}` (diagonal contraction)
- **4 Γ-Γ terms** that H₁/H₂ handle

**How do we:**
1. Cancel/contract the extra diagonal terms?
2. Match the goal shape to what H₁/H₂ expect?
3. Then apply your collectors?

---

## Comparison with Right Version

The right version (lines 3529-4033) uses a different structure:
- It's a **calc chain** with explicit fold steps
- Uses `pack_left_RiemannUp_core` helper
- Different organization of terms

The left version (what I'm working on) uses:
- **have statements** for H₁ and H₂
- Direct simp_rw for compatibility
- Needs to match your mixed collector strategy

---

## Options I See

### Option A: Insert cancellation step
Before H₁/H₂, add a step that:
```lean
have cancel_diag :
  sumIdx (fun k => Γ_{kθb} * Σ_{k_1} Γ_{k_1 r a} * g_{k_1 k})
+ ...
  = 0 + ...  -- Diagonal terms cancel
```

Then proceed with H₁/H₂?

### Option B: Adjust H₁/H₂ to handle both terms
Modify H₁/H₂ to expect the sum of both diagonal and off-diagonal terms?

### Option C: Use sumIdx_congr to separate
Apply `sumIdx_congr` to rewrite pointwise, separating the diagonal and off-diagonal parts?

### Option D: Different tactical approach
Abandon the H₁/H₂ approach and use a pure collector strategy from the start?

---

## Request

**Which approach should I use?**

Can you provide:
1. The exact rewrite sequence after `simp_rw [compat_r_a_e, compat_θ_a_e]`?
2. How to handle the diagonal `Γ k_1 · a * g_{k_1 k}` terms?
3. Whether H₁/H₂ need modification or if there's a step before them?

Or, alternatively:
4. Should I switch to a calc-chain approach like the right version?

---

## Current State

```lean
lemma regroup_left_sum_to_RiemannUp ... := by
  classical
  have compat_r_a_e : ...  ✅
  have compat_θ_a_e : ...  ✅
  simp_rw [compat_r_a_e, compat_θ_a_e]  ✅
  simp only [mul_add, add_mul, ...]  ✅  -- Distribution

  have H₁ : ... ✅  -- Contracts off-diagonal Γ-Γ
  have H₂ : ... ✅  -- Mirror of H₁

  -- ❌ BLOCKED HERE: How to proceed from expanded goal to collector application?
  sorry
```

---

## Files

- **Lemma**: `regroup_left_sum_to_RiemannUp` (line 4036)
- **Blocker**: Line 4100 (step ③)
- **H₁**: Lines 4070-4080
- **H₂**: Lines 4082-4093

---

**Prepared by**: Claude Code
**Date**: October 18, 2025
**Status**: Blocked on goal shape mismatch
**Need**: Guidance on rewrite sequence after compatibility expansion
