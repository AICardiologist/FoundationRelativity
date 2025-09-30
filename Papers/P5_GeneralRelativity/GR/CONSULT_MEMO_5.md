# Consultation Memo: Follow-up on Alternation Theorem Tactical Refinement

**Date:** September 29, 2025
**Re:** Update on implementation of suggested tactical patterns and remaining challenges
**Current Status:** Infrastructure added, but goal shape mismatch persists

## Executive Summary

Thank you for your detailed tactical guidance on the alternation theorem. We've successfully implemented all three suggested helpers and the "Fold, Descend, Normalize" pattern. While the infrastructure is now robust and well-structured, we're still encountering a pattern-matching issue where the goal state after Phase 2 doesn't match what our folding lemmas expect. The `simp only` step makes no progress, indicating a deeper shape mismatch.

## What We Successfully Implemented

### 1. Lightweight Helper Lemmas (lines 571-587) ✅

Added exactly as you specified:

```lean
@[simp] lemma add_sub_add_sub_assoc' (x y z w : ℝ) :
    x + (y - z) - w = (x + y) - (z + w) := by ring

@[simp] lemma sub_sub_eq_sub_add_sub' (x y z : ℝ) :
    x - y - z = x - (y + z) := by ring

@[simp] lemma sumIdx_fold_add_pairs_sub (A B C D : Idx → ℝ) :
    (sumIdx A + sumIdx B) - (sumIdx C + sumIdx D)
    = sumIdx (fun i => A i + B i) - sumIdx (fun i => C i + D i) := by
  rw [← sumIdx_fold_add A B, ← sumIdx_fold_add C D]
```

These compile perfectly and follow the principle of maintaining the canonical two-sum difference shape.

### 2. Updated Phase 3 Implementation ✅

Applied your suggested tactical pattern:

```lean
-- Phase 3: Fold, then normalize — without expanding `sumIdx`.
simp only [add_sub_add_sub_assoc', sub_sub_eq_sub_add_sub', sumIdx_fold_add_pairs_sub,
           add_comm, add_left_comm, add_assoc]

-- Residual pointwise arithmetic under the binders is trivial now.
ring
```

## The Problem That Persists

When building, we get:

```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:906:2: `simp` made no progress
```

This indicates that after Phase 2 (metric compatibility transformations), the goal doesn't have any of these patterns:
- `x + (y - z) - w` (for `add_sub_add_sub_assoc'`)
- `x - y - z` (for `sub_sub_eq_sub_add_sub'`)
- `(sumIdx A + sumIdx B) - (sumIdx C + sumIdx D)` (for `sumIdx_fold_add_pairs_sub`)

## What This Tells Us

The goal state after Phase 2 must have a different parenthesization or structure than we anticipated. The fact that `simp only` with these specific lemmas makes no progress means the goal doesn't contain any subterms matching these patterns.

## Specific Questions

1. **Goal Inspection**: Would it help to add a tactical probe to inspect the exact shape after Phase 2? Something like:
   ```lean
   -- After Phase 2 simplifications:
   trace "{goalState}"
   -- Or: fail "Goal shape: {goalState}"
   ```
   This would let us see the exact parenthesization and structure.

2. **Alternative Patterns**: Should we consider that the goal might have patterns like:
   - `((sumIdx A - sumIdx B) + sumIdx C) - sumIdx D`
   - `sumIdx A - (sumIdx B - (sumIdx C + sumIdx D))`
   - Or some other nested structure?

3. **Manual Exploration**: Would it be better to temporarily replace the `simp only` with manual `rw` attempts to discover which specific transformation is needed? For example:
   ```lean
   -- Try each lemma individually to see which applies:
   try { rw [add_sub_add_sub_assoc'] }
   try { rw [sub_sub_eq_sub_add_sub'] }
   try { rw [sumIdx_fold_add_pairs_sub] }
   ```

4. **Phase 2 Adjustment**: Should we modify the Phase 2 simplifications to produce a more predictable output shape? Perhaps removing some of the `add_comm, add_left_comm, add_assoc` normalizations that might be rearranging terms in unexpected ways?

## Current Impact

- **Error count**: 32 (still within budget of 50)
- **Infrastructure**: All helper lemmas compile and are theoretically sound
- **Alternation theorem**: Phases 1-2 work correctly; Phase 3 has documented `sorry`

## Request

Could you provide guidance on:

1. **Diagnostic approach**: Best way to inspect the actual goal shape after Phase 2
2. **Pattern coverage**: Whether we need additional folding lemmas for other parenthesizations
3. **Tactical alternatives**: If the "Fold, Descend, Normalize" pattern isn't matching, what's the next best approach?

The infrastructure you suggested is excellent and follows sound principles. We just need to bridge the gap between what Phase 2 produces and what our folding lemmas expect.

## What We Don't Need Help With

- The helper lemmas themselves (working correctly)
- Phase 1-2 implementation (functioning as intended)
- Overall proof strategy (architecturally sound)

Thank you for your continued guidance on this challenging tactical problem.