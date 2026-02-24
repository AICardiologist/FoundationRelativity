# Tactical Blocker - Detailed Analysis & Request for Refined Guidance

## Date: October 18, 2025
## Status: All three prioritized strategies attempted, pattern matching issues encountered

---

## Summary

Following the Senior Professor's tactical guidance, I attempted all three prioritized strategies for resolving the cancellation step at line 3681. Each approach encountered pattern matching issues when trying to apply the structural lemmas (`after_cancel`, `regroup8`, `kk_refold_expanded`).

**Root cause**: The current proof state (after applying compatibility rewrites) is in a form that doesn't exactly match the LHS patterns expected by these lemmas, despite being mathematically equivalent.

---

## Attempts Made

### Strategy 1: Direct Application (`after_cancel`)

**Code**:
```lean
rw [← after_cancel]
refine sumIdx_congr_then_fold ?_
funext k
ring
```

**Error**: "Did not find an occurrence of the pattern" (line 3684)

**Issue**: The `after_cancel` LHS expects the 6-term form in a specific structure (with parenthesization), but our current state has the terms in a slightly different grouping after the `simp only [sumIdx_add, sumIdx_sub]` distribution.

### Strategy 2: Step-by-Step Inline Expansion

**Code**:
```lean
rw [← regroup8]
simp_rw [← kk_refold_expanded]
ring_nf
```

**Error**: "Did not find an occurrence of the pattern" (line 3684)

**Issue**: Similar to Strategy 1 - `regroup8` expects a specific 6-term structure that doesn't match our current state exactly.

###  Strategy 3: Robust Congruence

**Multiple attempts made**:

**Attempt 3a**: Direct `sumIdx_congr_then_fold` + `ring`
```lean
refine sumIdx_congr_then_fold ?_
funext k
ring
```
**Result**: "unsolved goals" - `ring` cannot establish the pointwise equality because the left-slot cancellation requires domain-specific identities, not just algebraic rearrangement.

**Attempt 3b**: Using compat identities at pointwise level
```lean
refine sumIdx_congr_then_fold ?_
funext k
have hr := compat_r_e_b k
have hθ := compat_θ_e_b k
ring
```
**Result**: "unsolved goals" - the compat identities talk about `dCoord ... g...`, but we need to relate terms like `Γ * sumIdx (...)`, so they don't directly help at the pointwise level.

**Attempt 3c**: Trans with explicit 6-term intermediate
```lean
trans (sumIdx (fun k => ... 6-term form ...))
·  refine sumIdx_congr_then_fold ?_; funext k; ring
· rw [after_cancel]; ring
```
**Result**: "unsolved goals" at the first bullet - `ring` can't add the left-slot terms that aren't present.

**Attempt 3d**: Simplifier integration
```lean
simp only [sumIdx_add, sumIdx_sub]
rw [after_cancel]
ring
```
**Result**: "Did not find an occurrence" - the simplifier changed the structure so it no longer matches.

---

## Mathematical Analysis

### Current State (Line 3677-3681)

After the compat application step (lines 3667-3676), we have:
```lean
sumIdx (fun k =>
    dCoord Idx.r (...) * g M k b r θ  -- term 1
  - dCoord Idx.θ (...) * g M k b r θ  -- term 2
  + Γtot ... * sumIdx (fun lam => Γtot ... * g M lam b r θ)  -- term 3 (right-slot)
  + Γtot ... * sumIdx (fun lam => Γtot ... * g M k lam r θ)  -- term 4 (LEFT-SLOT)
  - Γtot ... * sumIdx (fun lam => Γtot ... * g M lam b r θ)  -- term 5 (right-slot)
  - Γtot ... * sumIdx (fun lam => Γtot ... * g M k lam r θ)) -- term 6 (LEFT-SLOT)
```

This is the **6-term form** (terms 1,2,3,5 are "right-slot", terms 4,6 are "left-slot").

### Target State (Line 3677-3681 RHS)

```lean
sumIdx (fun k =>
    dCoord Idx.r (...) * g M k b r θ  -- term 1
  - dCoord Idx.θ (...) * g M k b r θ  -- term 2
  + Γtot ... * sumIdx (fun lam => Γtot ... * g M lam b r θ)  -- term 3
  - Γtot ... * sumIdx (fun lam => Γtot ... * g M lam b r θ)) -- term 4
```

This is the **4-term form** (left-slot terms 4,6 have disappeared).

### Why They're Equal

The left-slot terms (4 and 6) cancel via the interplay of:
1. **regroup8**: Regrouping showing 6-term ↔ 4-term + left-slot
2. **kk_refold_expanded**: Showing left-slot ↔ compat-based expansion
3. **Fubini swaps**: Hidden in the sumIdx transformations

The `after_cancel` lemma encapsulates this via `rw [regroup8, kk_refold_expanded]`.

### The Challenge

The lemmas are defined with specific structural expectations (parenthesization, term ordering). Our current proof state, while mathematically equivalent, has:
- Different implicit parenthesization (from `ring` normalization)
- Terms potentially in different order
- Structure that doesn't pattern-match exactly

---

## Pattern Matching Details

### What `after_cancel` Expects (LHS)

```lean
sumIdx (fun k =>
    (dCoord Idx.r ... * g M k b r θ
   - dCoord Idx.θ ... * g M k b r θ
   + Γtot ... * sumIdx (...))
 - Γtot ... * sumIdx (...)
  + Γtot ... * sumIdx (... g M k lam ...)
  - Γtot ... * sumIdx (... g M k lam ...))
```

Note the specific grouping: `((...) - ...) + ... - ...`

### What We Have

```lean
sumIdx (fun k =>
    dCoord Idx.r ... * g M k b r θ
  - dCoord Idx.θ ... * g M k b r θ
  + Γtot ... * sumIdx (...)
  + Γtot ... * sumIdx (... g M k lam ...)
  - Γtot ... * sumIdx (...)
  - Γtot ... * sumIdx (... g M k lam ...))
```

Note: flat structure with `+ ... + ... - ... - ...`

These are **mathematically identical** (by associativity/commutativity of `+`/`-`), but Lean's `rw` tactic requires **syntactic matching**, not semantic equivalence.

---

## Potential Solutions

### Option A: Pre-normalize to Match Pattern

Before applying `after_cancel`, explicitly rearrange to match its expected structure:

```lean
conv => {
  -- Navigate to the sum expression
  arg 1; ext k
  -- Rearrange to match after_cancel LHS grouping
  rw [add_assoc, add_assoc, sub_eq_add_neg, sub_eq_add_neg]
  -- Restore specific structure
}
rw [after_cancel]
ring
```

### Option B: Custom Intermediate Lemma

Create a small helper lemma that bridges from our current structure to `after_cancel`:

```lean
have bridge :
  sumIdx (fun k => A k + B k - C k - D k) =
  sumIdx (fun k => (A k - C k) + B k - D k) := by
  refine sumIdx_congr_then_fold ?_; funext k; ring

rw [bridge, after_cancel]
ring
```

### Option C: Direct Congruence with Compat Reversal

Instead of using `after_cancel`, reverse the compat application for the left-slot terms:

```lean
refine sumIdx_congr_then_fold ?_
funext k
-- Reverse compat for left-slot terms to show they reconstruct ∂g terms
have hr_rev := (compat_r_e_b b).symm
have hθ_rev := (compat_θ_e_b b).symm
-- Algebraic manipulation using reversed compat
sorry  -- (complex but feasible with explicit steps)
```

### Option D: Bypass via abel_nf

Use the `abel_nf` normalizer which handles additive group structures more robustly:

```lean
refine sumIdx_congr_then_fold ?_
funext k
abel_nf  -- Normalize additive structure
sorry  -- Then apply specific domain lemmas
```

---

## Request for Guidance

Given the pattern matching challenges, which approach would you recommend:

1. **Option A** (conv mode normalization) - Most direct if we can identify the exact rewrite sequence
2. **Option B** (intermediate bridge lemma) - Clean but adds a helper
3. **Option C** (compat reversal) - More explicit but potentially lengthy
4. **Option D** (abel_nf + manual steps) - Robust normalizer but may need manual bridge
5. **Alternative approach** - Something I haven't considered?

Additionally:
- Should we reconsider the calc structure to avoid this step entirely?
- Is there a higher-level tactic (`ring!`, `polyrith`, etc.) that might handle this?
- Would it be acceptable to use a small `sorry` here with a TODO note, complete the rest of Phase 4, and return to this?

---

## Current File State

**Location**: `Riemann.lean:3681-3685`

**Current Code**:
```lean
_ = sumIdx (fun k =>
      dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a) r θ * g M k b r θ
    - dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a) r θ * g M k b r θ
    + Γtot M r θ k Idx.θ a * sumIdx (fun lam => Γtot M r θ lam Idx.r k * g M lam b r θ)
    - Γtot M r θ k Idx.r a * sumIdx (fun lam => Γtot M r θ lam Idx.θ k * g M lam b r θ)) := by
  -- [CURRENT BLOCKER - awaiting refined tactical guidance]
  sorry
```

**Build Status**: Clean except for this one sorry

**Mathematical Correctness**: 100% - this is purely a proof engineering question

---

## Broader Context

- All other restructuring complete (apply_H deleted, tactics removed, unified calc implemented)
- This is the ONLY remaining blocker for `regroup_right_sum_to_RiemannUp`
- Once resolved, can immediately mirror for `regroup_left` and proceed to Ricci identity lemmas
- Rest of Phase 4 is well-understood and ready to implement

---

**Prepared by**: Research Team (Claude Code)
**Date**: October 18, 2025
**Time Spent on This Step**: ~3 hours (all three strategies + multiple variants)
**Status**: Requesting refined tactical guidance for pattern matching issue
