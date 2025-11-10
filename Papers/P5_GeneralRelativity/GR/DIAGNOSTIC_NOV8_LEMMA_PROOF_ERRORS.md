# DIAGNOSTIC: Lemma Proof Errors After Type Fix

**Date**: November 8, 2025
**Status**: 🟡 **Type fix successful, but proof goals remain unsolved**

---

## Executive Summary

Paul's type signature fix (`M : Manifold` → `M : ℝ`) successfully eliminated all TYPE MISMATCH errors. However, there are still **3 errors** in the new lemmas related to unsolved proof goals. The type signatures are now correct, but the proof tactics need adjustment.

**Total errors**: 21 (3 in new lemmas + 18 baseline)
**New lemma errors**: 3
- Line 1754: `unsolved goals` in `sumIdx_collapse_left_metric`
- Line 1760: `unsolved goals` in `sumIdx_cross_collapse_left`
- Line 8834: `simp` failed in `hb_plus` (depends on lemmas above)

---

## Error Breakdown

### Error 1: Line 1754 (`sumIdx_collapse_left_metric`)

**Location**: Final calc step in `sumIdx_collapse_left_metric`

**Code**:
```lean
_   = A ρ * g M ρ ρ r θ := by
        simp [mul_comm (A ρ), mul_assoc]
```

**Error**: `unsolved goals`

**Goal state**:
```lean
M r θ : ℝ
A : Idx → ℝ
ρ : Idx
⊢ (sumIdx fun e =>
      if e = ρ then ...)  = A ρ * g M ρ ρ r θ
```

**Problem**: The `simp` tactic is not applying `sumIdx_delta_right` to collapse the Kronecker delta sum.

**Root cause**: After the previous calc step inserted the delta `(if e = ρ then 1 else 0)`, the goal needs `sumIdx_delta_right` to collapse, but `simp` isn't finding it or applying it correctly.

---

### Error 2: Line 1760 (`sumIdx_cross_collapse_left`)

**Location**: Proof body in `sumIdx_cross_collapse_left`

**Code**:
```lean
lemma sumIdx_cross_collapse_left (M : ℝ) (r θ : ℝ) (L A : Idx → ℝ) :
  sumIdx (fun ρ => L ρ * sumIdx (fun e => A e * g M ρ e r θ))
    = sumIdx (fun ρ => g M ρ ρ r θ * (L ρ * A ρ)) := by
  refine sumIdx_congr (fun ρ => ?_)
  simp [sumIdx_collapse_left_metric M r θ A ρ, mul_assoc, mul_comm (g M ρ ρ r θ)]
```

**Error**: `unsolved goals`

**Goal state**:
```lean
M r θ : ℝ
L A : Idx → ℝ
ρ : Idx
⊢ (L ρ *
      sumIdx fun e =>
        A e *
          (match (motive := Idx → Idx → ℝ → ℝ → ℝ) ρ, e with
            | t, t => fun r _θ => -f M r
            | Idx.r, Idx.r => fun r _θ => (f M r)⁻¹
            | Idx.θ, Idx.θ => fun r _θ => r ^ 2 ...)
```

**Problem**: The `simp` tactic is unfolding `g M ρ e r θ` into its full definition (a match statement) instead of applying `sumIdx_collapse_left_metric`.

**Root cause**: `simp` is too aggressive and unfolds `g` before it can apply `sumIdx_collapse_left_metric`.

---

### Error 3: Line 8834 (`hb_plus`)

**Location**: Final step in `hb_plus` helper

**Code**:
```lean
simpa [hneg_b, hcomm, hR] using ΓΓ_cross_collapse_b M r θ μ ν a b
```

**Error**: `Tactic 'simp' failed with a nested error`

**Problem**: The `ΓΓ_cross_collapse_b` lemma depends on `sumIdx_cross_collapse_left`, which has unsolved goals. Since the lemma doesn't compile, it can't be used here.

---

## Root Cause Analysis

### The Type Fix Worked ✅

Paul's fix successfully changed:
- `M : Manifold` → `M : ℝ` in all three lemmas
- Result: NO more "application type mismatch" errors
- The functions `g M ...` and `Γtot M ...` now type-check correctly

### The Proof Tactics Need Adjustment ❌

The issue is that the proof tactics (`simp`) are either:
1. **Not aggressive enough**: Not applying `sumIdx_delta_right` (line 1754)
2. **Too aggressive**: Unfolding `g` definition too early (line 1760)

---

## Proposed Fixes

### Fix for Line 1754

The final calc step needs to apply `sumIdx_delta_right` explicitly:

**Option A** - Use `exact`:
```lean
_   = A ρ * g M ρ ρ r θ := by
        exact sumIdx_delta_right (fun e => A e * g M ρ e r θ) ρ
```

**Option B** - Guide `simp` with more explicit lemmas:
```lean
_   = A ρ * g M ρ ρ r θ := by
        simp only [sumIdx_delta_right, mul_comm (A ρ), mul_assoc]
```

### Fix for Line 1760

Prevent `g` from unfolding by using `simp only` or avoiding `simp` entirely:

**Option A** - Apply lemma directly without `simp`:
```lean
lemma sumIdx_cross_collapse_left (M : ℝ) (r θ : ℝ) (L A : Idx → ℝ) :
  sumIdx (fun ρ => L ρ * sumIdx (fun e => A e * g M ρ e r θ))
    = sumIdx (fun ρ => g M ρ ρ r θ * (L ρ * A ρ)) := by
  refine sumIdx_congr (fun ρ => ?_)
  rw [sumIdx_collapse_left_metric M r θ A ρ]
  ring
```

**Option B** - Use `simp only` with restricted lemma set:
```lean
simp only [sumIdx_collapse_left_metric M r θ A ρ, mul_assoc, mul_comm]
```

### Fix for Line 8834

Once the two lemmas above are fixed, this should resolve automatically.

---

## Action Items

1. **Fix line 1754**: Apply `sumIdx_delta_right` explicitly
2. **Fix line 1760**: Prevent `g` from unfolding during simplification
3. **Verify line 8834**: Should work once dependencies compile

---

## Current Error Count

### New Lemma Errors (3)
1. Line 1754: `sumIdx_collapse_left_metric` - unsolved goals
2. Line 1760: `sumIdx_cross_collapse_left` - unsolved goals
3. Line 8834: `hb_plus` - depends on lemmas above

### Baseline Errors (18)
- Lines 8841, 8991, 9006, 9023, 9027, 9058, 9109, 9257, 9272, 9290, 9294, 9334, 9339, 9580, 9781, 9795, 9864, 9975

**Total**: 21 errors

---

## Key Findings

### What Worked ✅
- Type signature fix: `M : ℝ` eliminated all type mismatch errors
- All three lemma signatures are now correct
- The lemma structure and approach are sound

### What Needs Work ❌
- Proof tactics need to be more surgical
- `simp` is either too aggressive (unfolds too much) or not aggressive enough (doesn't apply needed lemmas)
- Need explicit application of `sumIdx_delta_right` and controlled use of `sumIdx_collapse_left_metric`

---

## Recommendation

Ask Paul for guidance on the proof tactics:
1. Should we use `exact` instead of `simp` for the delta collapse?
2. Should we use `rw` + `ring` instead of `simp` to prevent unwanted unfolding?
3. Is there a `simp` configuration that would work better?

The mathematical content is correct - this is purely a tactical issue in how we're instructing Lean to apply the reasoning steps.

---

**Status**: 🟡 **Type fix successful, awaiting proof tactic adjustments**
**Next**: Apply proposed fixes or consult Paul on preferred tactical approach
