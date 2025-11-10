# Diagnostic Report: Paul's Tactical Fixes - Integration Issue - November 1, 2025

**Date**: November 1, 2025
**Build**: `build_paul_tactical_fixes_nov1.txt`
**Total Errors**: 27 (up from 24)
**Block A Errors**: 13 (up from 11)
**Status**: 🔴 **INTEGRATION ERROR** - Missing lemma references

---

## Executive Summary

I applied all four of Paul's tactical fix patches exactly as provided, but the build shows **increased** errors rather than the expected decrease. The root cause is a **structural integration mismatch**: Paul's calc chains were meant to be wrapped as `have` statements that produce named lemmas, but I applied them as standalone calc chains, causing downstream references to undefined lemmas.

**Critical Finding**: Lines 8812 and 9070 reference `h_insert_delta_for_b` and `h_insert_delta_for_a`, but these lemmas no longer exist because the calc chains replaced them without preserving the named bindings.

---

## Error Analysis

### Error Count Comparison

| Stage | Total Errors | Block A Errors | Status |
|-------|--------------|----------------|--------|
| Paul's Structural Fix (corrected) | 24 | 11 | Baseline |
| **Paul's Tactical Fixes (current)** | **27** | **13** | **REGRESSION** ⚠️ |

**Net Change**: +3 total errors, +2 Block A errors

---

## Root Cause: Missing Lemma Bindings

### The Problem

**Line 8812** (b-branch):
```lean
rw [h_insert_delta_for_b, ← sumIdx_add_distrib]
```
**Error**: `h_insert_delta_for_b` is not defined

**Line 9070** (a-branch):
```lean
rw [h_insert_delta_for_a, ← sumIdx_add_distrib]
```
**Error**: `h_insert_delta_for_a` is not defined

### What I Did

I replaced the entire `have h_insert_delta_for_b` statement (lines 8713-8758) with Paul's calc chain:

```lean
-- OLD:
have h_insert_delta_for_b :
  sumIdx (fun ρ => ... * g M ρ b r θ)
  = sumIdx (fun ρ => ... * g M ρ b r θ * (if ρ = b then 1 else 0)) := by
  classical
  apply sumIdx_congr
  ...

-- NEW (what I applied):
classical
set X : Idx → ℝ := fun ρ => ...
have hswap : ... := ...
have hcontr : ... := ...
have hdelta : ... := ...
calc
  sumIdx (fun ρ => ... ) = ...
  _ = ...
  _ = ...
```

**Issue**: The calc chain doesn't bind a name `h_insert_delta_for_b`, so the later `rw [h_insert_delta_for_b]` fails.

---

## What Should Have Been Done

### Option A: Wrap calc as have body

```lean
have h_insert_delta_for_b :
  sumIdx (fun ρ =>
    - ( ( dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ
         - dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ
         + sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
         - sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) )
       * g M ρ b r θ))
  = sumIdx (fun ρ =>
    - ( ( dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ
         - dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ
         + sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
         - sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) )
       * g M ρ b r θ) * (if ρ = b then 1 else 0)) := by
  classical
  -- Paul's calc chain goes here
  set X : Idx → ℝ := fun ρ => ...
  have hswap : ... := ...
  have hcontr : ... := ...
  have hdelta : ... := ...
  calc
    sumIdx (fun ρ => ...) = sumIdx (fun ρ => X ρ * g M ρ b r θ) := ...
    _ = X b * g M b b r θ := ...
    _ = sumIdx (fun ρ => (X ρ * g M ρ b r θ) * (if ρ = b then 1 else 0)) := ...
    _ = sumIdx (fun ρ => ...) := ...
```

### Option B: Extract equality from calc

```lean
classical
set X : Idx → ℝ := fun ρ => ...
have hswap : ... := ...
have hcontr : ... := ...
have hdelta : ... := ...

have h_insert_delta_for_b : (start_expr) = (end_expr) :=
  calc (start_expr) = ... _ = ... _ = (end_expr)
```

---

## Block A Errors Detail

### b-branch Errors (7 errors)
- **Line 8748**: unsolved goals - First calc step fails to unify
- **Line 8757**: unsolved goals - Fourth calc step fails
- **Line 8773**: unsolved goals - scalar_finish downstream cascade
- **Line 8803**: unsolved goals - payload glue downstream
- **Line 8808**: Type mismatch - `exact sumIdx_congr scalar_finish` wrong context
- **Line 8812**: Tactic 'rewrite' failed - **h_insert_delta_for_b undefined**
- **Line 8841**: unsolved goals - downstream cascade

### a-branch Errors (6 errors)
- **Line 9007**: Type mismatch - similar to 8808
- **Line 9023**: unsolved goals - First calc step fails
- **Line 9034**: unsolved goals - Fourth calc step fails
- **Line 9050**: unsolved goals - scalar_finish downstream
- **Line 9066**: Type mismatch - `exact sumIdx_congr scalar_finish` wrong context
- **Line 9070**: Tactic 'rewrite' failed - **h_insert_delta_for_a undefined**

---

## Additional Issue: Calc Step Unification

Even if I fix the missing lemma bindings, there are errors at lines 8748, 8757, 9023, 9034 where the calc steps fail to unify. The error message shows:

```lean
⊢ -(g M b ρ r θ * (...)) = g M b ρ r θ * (...)
```

This suggests the `simp [X, mul_comm, mul_left_comm, mul_assoc]` isn't properly distributing the negation or reordering the factors.

---

## Questions for Paul

### Q1: Calc Chain Integration

Should the calc chains be:
1. **Wrapped** as the proof body of `have h_insert_delta_for_b : (lhs) = (rhs) := by calc ...`?
2. **Extracted** by binding the final equality with a name after the calc?
3. **Replaced entirely** with a different proof structure that doesn't use `h_insert_delta_for_b` later?

### Q2: Negation Distribution

The calc step at line 8748 is trying to show:
```lean
sumIdx (fun ρ => - ( ( big_expr ) * g M ρ b r θ))
= sumIdx (fun ρ => X ρ * g M ρ b r θ)
```

But `X ρ = - ( big_expr )`, so this should be:
```lean
sumIdx (fun ρ => (- big_expr) * g M ρ b r θ))
= sumIdx (fun ρ => X ρ * g M ρ b r θ)
```

The tactic `simp [X, mul_comm, mul_left_comm, mul_assoc]` doesn't handle negation distribution. Should this be:
- `simp [X, neg_mul, mul_comm, mul_left_comm, mul_assoc]`?
- `ring` instead of `simp`?
- A `show` statement first to establish the goal shape?

### Q3: Payload Glue Context

Lines 8808 and 9066 use `exact sumIdx_congr scalar_finish`, but the error says "Type mismatch". The context after `simp only [nabla_g, RiemannUp, sub_eq_add_neg]` might not match the shape that `sumIdx_congr scalar_finish` produces. Should there be:
1. Additional simp lemmas before `exact`?
2. A different tactic like `convert`?
3. A normalization step?

---

## Current File State

### Lines 8710-8760 (b-branch delta insertion)
```lean
    have h_insert_delta_for_b := by
      classical
      -- Package the scalar core so the metric sits alone for contraction/delta steps.
      set X : Idx → ℝ := fun ρ =>
        - ( dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ
            - dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ
            + sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
            - sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) )

      -- Swap the metric indices under the binder: g_{ρ b} = g_{b ρ}.
      have hswap : ... := ...
      have hcontr : ... := ...
      have hdelta : ... := ...

      -- Assemble: rewrite both sides to X b · g_{bb} and conclude by symmetry.
      calc
        sumIdx (fun ρ => - ( ( ... ) * g M ρ b r θ))
            = sumIdx (fun ρ => X ρ * g M ρ b r θ) := by  -- LINE 8748 FAILS HERE
                apply sumIdx_congr; intro ρ; simp [X, mul_comm, mul_left_comm, mul_assoc]
        _   = X b * g M b b r θ := (hswap.trans hcontr)
        _   = sumIdx (fun ρ => (X ρ * g M ρ b r θ) * (if ρ = b then 1 else 0)) := hdelta.symm
        _   = sumIdx (fun ρ => - ( ( ... ) * g M ρ b r θ) * (if ρ = b then 1 else 0)) := by  -- LINE 8757 FAILS HERE
                apply sumIdx_congr; intro ρ; simp [X, mul_comm, mul_left_comm, mul_assoc]
```

**Note**: `h_insert_delta_for_b := by` doesn't include a type annotation, so Lean infers the type from the calc result. But this might not match what's expected later.

---

## Recommended Next Steps

### Immediate Fix (for me to apply)

1. **Add explicit type annotations** to `have h_insert_delta_for_b` and `have h_insert_delta_for_a`
2. **Fix negation handling** in the calc step simplifications (use `ring` or `neg_mul`)
3. **Verify payload glue context** matches `sumIdx_congr scalar_finish` output

### Request to Paul

Please provide either:
1. **Corrected calc integration**: Explicit `have h_insert_delta_for_b : (lhs) = (rhs) := by calc ...` with full LHS/RHS
2. **Alternative proof structure**: If the calc chains should replace downstream usage of `h_insert_delta_for_b` entirely
3. **Tactical fixes for the calc steps**: How to make lines 8748, 8757, 9023, 9034 unify correctly

---

**Prepared by**: Claude Code (Lean 4 Assistant)
**Build File**: `build_paul_tactical_fixes_nov1.txt`
**Date**: November 1, 2025
**Status**: Integration error - awaiting Paul's structural guidance

---

**End of Diagnostic Report**
