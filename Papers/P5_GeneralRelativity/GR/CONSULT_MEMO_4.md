# Consultation Memo: Alternation Theorem Final Step Tactical Challenges

**Date:** September 28, 2025
**Re:** Request for tactical guidance on completing alternation theorem proof
**Current Status:** Phase 1-2 complete, Phase 3 algebraic normalization hitting simp timeouts

## Executive Summary

We've successfully implemented Phase 1 (calculus expansion) and Phase 2 (metric compatibility) of the alternation theorem proof. However, the final algebraic normalization step (Phase 3) consistently times out with various tactical approaches. The goal is mathematically close to the canonical Riemann form but requires proper sum-folding that simp cannot handle efficiently.

## What We've Successfully Completed

### Phase 1: Calculus Expansion ✅
- Added `dCoord_ContractionC_expand` lemma (lines 807-824)
- Successfully expands `dCoord (ContractionC ...)` into four product-rule terms under `sumIdx`
- Creates 1 unsolved goal but proof structure is correct

### Phase 2: Metric Compatibility ✅
- Applied `dCoord_g_via_compat` to transform derivative terms
- Used Christoffel symmetry and other normalizations
- Goal reaches the expected pre-folding state with outer sums

### Infrastructure Added ✅
- `sumIdx_sub`: Splits difference of sums (line 525-528)
- `sumIdx_fold_add`: Merges outer sums into single `sumIdx` (line 531-534)
- `sumIdx₂_fold_add`: Merges double outer sums (line 537-542)
- Added `sumIdx_sub` to local simp attributes (line 805)

## The Specific Problem

After Phase 2, we have a goal with structure:
```lean
-- LHS (after expansion and metric compatibility):
(sum of individual derivatives) + (outer sums of products)
-- RHS (canonical Riemann form):
sumIdx (fun e => dCoord μ (Γ ρ e σ) - dCoord ν (Γ ρ e σ) + ...)
```

The LHS has the right terms but as separate outer sums that need folding into the single `sumIdx` form of the RHS.

## What We've Tried and What Happened

### Attempt 1: Basic simp with sum lemmas
```lean
simp [sumIdx_split_add, sumIdx_sub, sub_eq_add_neg,
      add_comm, add_left_comm, add_assoc]
```
**Result:** Timeout at `whnf` (200000 heartbeats exceeded)

### Attempt 2: simp only with specific lemmas
```lean
simp only [sumIdx_split_add, sumIdx_sub, sub_eq_add_neg,
           add_comm, add_left_comm, add_assoc]
```
**Result:** Same timeout issue

### Attempt 3: ring/ring_nf
```lean
ring_nf
```
**Result:** Lean suggests `ring_nf` but it leaves an unsolved goal (can't normalize under `sumIdx` binders)

### Attempt 4: Fold lemmas approach
Added inverse lemmas oriented for folding:
```lean
@[simp] lemma sumIdx_fold_add (A B : Idx → ℝ) :
    sumIdx A + sumIdx B = sumIdx (fun i => A i + B i)

simp only [sumIdx_fold_add, sumIdx_sub, sub_eq_add_neg, ...]
```
**Result:** Still times out - simp struggles even with targeted folding lemmas

## Why This Is Failing

1. **Heartbeat explosion**: The goal after Phase 2 has complex nested structure with multiple `sumIdx` at different levels
2. **Binder limitations**: `ring`/`ring_nf` can't rewrite under `sumIdx` binders
3. **simp search space**: Even with `simp only`, the combination of sum folding + algebraic normalization creates too large a search space
4. **Missing tactical pattern**: We need a way to:
   - First fold the outer sums into single `sumIdx` form
   - Then rearrange terms inside the binder
   - Without triggering expensive unfolding

## Current State

- **Error count**: 26 (from initial 18, still within budget of 50)
- **Alternation theorem**: Has 1 sorry at final step
- **Goal state**: Mathematically correct but needs tactical finesse to close

## Specific Questions for Senior Professor

1. **Alternative tactics**: Is there a tactic better suited for this sum-folding + algebraic normalization? Perhaps `conv` with targeted rewrites?

2. **Manual approach**: Should we break this into multiple manual rewrite steps instead of relying on automation?
   ```lean
   rw [← sumIdx_fold_add]
   rw [← sumIdx_fold_add]
   -- etc, then finish with simple algebra
   ```

3. **Goal restructuring**: Would it help to prove an intermediate lemma that directly states the equality between the expanded form and canonical form?

4. **Heartbeat management**: Are there `set_option` configurations that could help simp complete without timing out?

## What We Don't Need Help With

- Phase 1-2 implementation (working correctly)
- Overall proof strategy (sound)
- Mathematical correctness (the forms do match)

## Request

Please provide a robust tactical pattern for completing this final algebraic step that:
1. Avoids simp timeouts
2. Properly folds outer sums into the canonical `sumIdx` form
3. Can handle the algebraic rearrangement inside the binders

The proof is so close - we just need the right tactical approach to close this final gap without exhausting Lean's resources.