# Report to Junior Professor: Phase 3 Tactical Implementation - Findings and Blockage

**Date**: October 6, 2025
**Topic**: Implementation attempt of modular strategy for diagonal Ricci cases
**Status**: Tactical blockage identified - need guidance on correct approach
**Error Count**: 4 (one per diagonal case - all same issue)

---

## Executive Summary

I attempted to implement your tactical recipe for the diagonal Ricci cases using the modular strategy with Phase 2 component lemmas. **The `raise` lemmas now work successfully**, but I've discovered a fundamental misunderstanding about the structure of the problem.

**Key Discovery**: After expanding `sumIdx`, the goal already contains **covariant** Riemann tensor components (R_ρaρb), not mixed RiemannUp components (R^ρ_aρb). This means the `raise` lemmas that convert RiemannUp to (g)⁻¹ × Riemann are not needed!

---

## What I Implemented

Following your recipe, I refactored all 4 diagonal cases with this structure:

```lean
case t.t =>
  -- Step 1: Expand sum, drop R^t_ttt = 0
  simp only [sumIdx_expand]
  simp only [Riemann_first_equal_zero_ext M r θ h_ext h_sin_nz]

  -- Step 2: Derive RiemannUp = (g)⁻¹ * Riemann (SUCCESSFUL!)
  have raise_r : RiemannUp M r θ Idx.r Idx.t Idx.r Idx.t
      = (g M Idx.r Idx.r r θ)⁻¹ * Riemann M r θ Idx.r Idx.t Idx.r Idx.t := by
    have h := Riemann_contract_first M r θ Idx.r Idx.t Idx.r Idx.t
    field_simp [grr_ne]
    rw [h]
    ring

  -- [similar for raise_θ, raise_φ]

  -- Step 3: Try to use raise lemmas
  rw [raise_r, raise_θ, raise_φ]  -- ❌ FAILS!
```

---

## The Problem: Mismatch Between Expected and Actual Goal

### After Step 1 (sumIdx_expand), the actual goal is:

```lean
⊢ 0 + Riemann M r θ Idx.r t Idx.r t + Riemann M r θ Idx.θ t Idx.θ t + Riemann M r θ φ t φ t = 0
```

**This is already covariant Riemann!** Not RiemannUp.

### But `raise_r` is defined as:

```lean
raise_r : RiemannUp M r θ Idx.r Idx.t Idx.r Idx.t = (g M Idx.r Idx.r r θ)⁻¹ * Riemann M r θ Idx.r Idx.t Idx.r Idx.t
```

### So when we try `rw [raise_r]`, Lean says:

```
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  RiemannUp M r θ t Idx.r t Idx.r
in the target expression
  Riemann M r θ t Idx.r t Idx.r + 0 + ...
```

**The goal has `Riemann` (covariant), but `raise_r` rewrites `RiemannUp` (mixed)!**

---

## Analysis: Understanding the Mismatch

I believe the issue is with how `RicciContraction` is defined:

```lean
noncomputable def RicciContraction (M r θ : ℝ) (a b : Idx) : ℝ :=
  sumIdx (fun ρ => Riemann M r θ ρ a ρ b)
```

**This sums over `Riemann` (fully covariant 4-index tensor), not `RiemannUp` (mixed tensor).**

So the contraction is:
```
R_ab = Σ_ρ R_ρaρb  (covariant)
```

**Not**:
```
R_ab = Σ_ρ R^ρ_aρb  (mixed)
```

---

## What This Means

The actual mathematical operation happening is:
```
R_tt = Riemann(r,t,r,t) + Riemann(θ,t,θ,t) + Riemann(φ,t,φ,t)
```

All terms are **fully covariant** (4 lower indices).

To use the Phase 2 component lemmas, we need to:
1. Apply symmetries to get standard index order
2. Directly use the `_eq` lemmas (which give covariant values)
3. Simplify

**We don't need the inverse metric at all** because we're already working with covariant components!

---

## Attempted Fixes and What I Learned

### Fix Attempt 1: `congrArg` pattern (as you suggested)
- **Result**: Successfully derived `raise` lemmas ✅
- **Problem**: Can't apply them because goal has wrong tensor type ❌

### Fix Attempt 2: Pattern `field_simp + linear_combination`
- **Result**: `linear_combination` doesn't work with the equation form
- **Solution**: Use `rw [h]; ring` instead ✅

### Fix Attempt 3: Try to rewrite with raise lemmas
- **Result**: Pattern not found (as shown above) ❌

---

## Question for Junior Professor

**Is the RicciContraction definition correct?**

Option A: Current definition is correct (sums covariant Riemann)
```lean
-- If so, the solution is:
case t.t =>
  simp only [sumIdx_expand, Riemann_first_equal_zero_ext]

  -- Apply symmetries to normalize index order
  have h_rt : Riemann M r θ Idx.r Idx.t Idx.r Idx.t = Riemann M r θ Idx.t Idx.r Idx.t Idx.r := by [...]
  have h_θt : Riemann M r θ Idx.θ Idx.t Idx.θ Idx.t = Riemann M r θ Idx.t Idx.θ Idx.t Idx.θ := by [...]
  have h_φt : Riemann M r θ Idx.φ Idx.t Idx.φ Idx.t = Riemann M r θ Idx.t Idx.φ Idx.t Idx.φ := by [...]

  rw [h_rt, h_θt, h_φt]

  -- Use Phase 2 component lemmas directly
  rw [Riemann_trtr_eq, Riemann_tθtθ_eq, Riemann_tφtφ_eq]

  -- Simplify
  simp only [g, f]
  field_simp [...]
  ring
```

Option B: Definition should use RiemannUp (mixed tensor)
```lean
-- Then we need to redefine:
noncomputable def RicciContraction (M r θ : ℝ) (a b : Idx) : ℝ :=
  sumIdx (fun ρ => RiemannUp M r θ ρ a ρ b)

-- And the modular strategy with inverse metric would work as you described
```

---

## Current File Status

- **Lines modified**: 5156-5398 (all 4 diagonal cases)
- **Raise lemmas**: All working correctly (9 lemmas total, 3 per case except case t.t) ✅
- **Symmetry lemmas**: Already implemented from previous attempt ✅
- **Blocking issue**: Can't apply raise lemmas to covariant Riemann terms ❌

---

## Files for Reference

- **Main file**: `Papers/P5_GeneralRelativity/GR/Riemann.lean`
- **Diagonal cases**: Lines 5156-5398
- **Example error**: Case t.t at line 5196 (rw [raise_r, raise_θ, raise_φ])
- **Build log**: `/tmp/final_phase3_build.txt`

---

## Request

Please clarify:

1. **Is `RicciContraction` defined correctly** (summing covariant Riemann)?
2. **If yes**: Should I skip the `raise` lemmas entirely and go straight to symmetries + _eq lemmas?
3. **If no**: Should we refactor `RicciContraction` to use `RiemannUp` instead?

Your guidance will determine which path forward is correct. The tactical machinery (raise lemmas, symmetries) is all working - we just need to know the right mathematical structure to apply it to.

Thank you!

---

**Session**: Claude Code
**Build Command Used**: `lake build` (as requested)
**Total Errors**: 4 (down from 7, resolved raise lemma issues + 3 pre-existing infrastructure errors)
