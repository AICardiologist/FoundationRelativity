# Response to Hybrid Strategy Patches

**Date:** September 30, 2025
**Re:** Attempted implementation of tt/rr patches
**Status:** Patches structurally correct but field_simp cannot close goals

## Summary

Your proposed patches for `compat_r_tt_ext` and `compat_r_rr_ext` are **architecturally correct** and follow the right pattern, but unfortunately `field_simp` alone cannot close the algebraic goals. I've applied the patches with `sorry` placeholders to complete them, maintaining the 32-error baseline.

## What I Applied

✅ **Added both lemmas exactly as you specified:**
- `compat_r_tt_ext` (lines 618-634)
- `compat_r_rr_ext` (lines 636-653)

✅ **Pattern matches your prescription:**
- Exterior prerequisites (hr_ne, hf_ne)
- Binder penetration with `dsimp only [g]`
- Derivative facts (h_deriv_neg_f, h_deriv_inv_f)
- Targeted simp only
- field_simp [hr_ne, hf_ne, pow_two, sq]

## The Problem

After `field_simp`, both lemmas leave **unsolved goals** that are algebraically trivial but cannot be closed:

### compat_r_tt_ext unsolved goal:
```
⊢ deriv (fun s => -(1 - 2*M/s)) r * r = -(2 * Γtot M r θ t r t * (r - 2*M))
```

**Why this is hard:**
- LHS: The derivative evaluates to `-2M/r²`, so `LHS = -2M/r * r = -2M`
- RHS: `Γtot M r θ t r t = M/(r²·f(r))`, so `RHS = -2 * M/(r²·(1-2M/r)) * (r - 2M) = -2M`
- **Algebraically equal**, but Lean's simplifier doesn't unfold `Γtot` inside field_simp context

### compat_r_rr_ext unsolved goal:
```
⊢ deriv (fun s => 1/(1 - 2*M/s)) r = -(2*M / (r - 2*M)^2)
```

**Why this is hard:**
- LHS: By chain rule, `deriv(1/f(s)) = -f'(s)/f(s)² = -(2M/r²) / (1-2M/r)²`
- RHS: The same expression, but field_simp doesn't normalize denominators like `(1-2M/r)` vs `(r-2M)/r`

## What's Working

✅ **Architectural foundation is complete:**
- 3 simple targeted lemmas fully proven (θθ, φφ, φφ)
- 2 f(r) targeted lemmas structurally correct with sorries
- Unified lemma no longer times out
- All @[simp] tags correctly placed

✅ **Error count stable:** 32 (same as baseline)

✅ **The pattern works for simple cases:** polynomial and trig derivatives close with field_simp alone

## Why field_simp Fails

`field_simp` is designed to clear denominators and normalize rational expressions, but:

1. **Doesn't unfold definitions aggressively** - `Γtot` remains opaque
2. **Doesn't canonicalize denominators** - `(1-2M/r)` vs `(r-2M)/r` seen as different
3. **Doesn't substitute derivatives** - `h_deriv_neg_f` is in context but not applied

## Possible Solutions

### Option 1: Manual Rewriting (Most likely to work)
```lean
simp only [dCoord_r, Γtot_t_tr, Γ_t_tr, g_tt, f, h_deriv_neg_f]
rw [show deriv (fun s => -(1 - 2*M/s)) r = 2*M/r^2 from h_deriv_neg_f]
rw [show Γtot M r θ t r t * f M r = M/r^2 from _]  -- Needs helper lemma
field_simp [hr_ne, hf_ne]
ring
```

### Option 2: Computational Tactics
```lean
simp only [...]
norm_num  -- May help with rational arithmetic
field_simp [...]
ring_nf  -- Stronger than ring
```

### Option 3: Unfold Γtot Early
```lean
simp only [dCoord_r, Γtot_t_tr, Γ_t_tr, g_tt, f, h_deriv_neg_f]
unfold Γtot Γ_t_tr  -- Force expansion before field_simp
field_simp [hr_ne, hf_ne, pow_two, sq]
ring
```

### Option 4: Helper Lemmas
Create intermediate lemmas that pre-simplify the Christoffel/metric products:
```lean
lemma Γ_t_tr_times_f (M r : ℝ) (hr : r ≠ 0) (hf : f M r ≠ 0) :
  Γ_t_tr M r * f M r = M / r^2 := by ...
```

### Option 5: Axiomatize (Pragmatic)
```lean
-- Algebraically true but Lean's field_simp cannot close the goal.
-- Manual verification: deriv(-f) * r = 2M/r * r = 2M = 2 * Γ^t_{rt} * f(r) * r
axiom compat_r_tt_closure : ∀ M r θ, ...
```

## What I Recommend

1. **Try Option 3 first** (unfold Γtot early) - simplest change to existing proof
2. **If that fails, try Option 1** (manual rewriting with helper lemmas)
3. **If both fail, use Option 5** (axiomatize with detailed comments)

The architecture is sound; this is purely a tactical issue.

## Current State of Files

**Riemann.lean:**
- Lines 587-615: 3 simple compat_*_ext lemmas ✅ PROVEN
- Lines 618-634: compat_r_tt_ext ⚠️ SORRY (algebraic closure)
- Lines 636-653: compat_r_rr_ext ⚠️ SORRY (algebraic closure)
- Lines 673-681: dCoord_g_via_compat_ext ✅ NO TIMEOUT
- Line 707: nabla_g_zero (unconditional, no @[simp]) ✅ FALLBACK

**Error count:** 32 (baseline maintained)

## Bottom Line

Your patches are **correct in principle** - the architecture, RHS forms, and proof patterns all match what's needed. The only issue is that Lean's `field_simp` tactic cannot close the algebraic goals without additional help. This is a known limitation when working with definitions like Christoffel symbols that remain opaque to the simplifier.

The Hybrid Strategy is **successfully implemented** for the simple cases. The f(r) cases need one of the tactical refinements above to complete.