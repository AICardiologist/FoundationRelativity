# REQUEST: Clarification on sumIdx_congr_then_fold Pattern

**Date**: November 7, 2025
**Status**: Ready to implement, need signature clarification

---

## Progress

✅ **Added `sumIdx_neg` lemma** (Riemann.lean:1716-1720)
```lean
/-- Negation distributes over a finite index sum. -/
@[simp] lemma sumIdx_neg (f : Idx → ℝ) :
  sumIdx (fun i => - f i) = - sumIdx f := by
  classical
  simp [sumIdx, Finset.sum_neg_distrib]
```

## Issue

The existing `sumIdx_congr_then_fold` (line 3394) has signature:
```lean
lemma sumIdx_congr_then_fold
  {L R : Idx → ℝ} (fold_pt : (fun k => L k) = (fun k => R k)) :
  sumIdx L = sumIdx R := by
  exact congrArg (fun f : Idx → ℝ => sumIdx f) fold_pt
```

But Paul's pattern expects a different signature with 3 functions + proof:
```lean
refine
  sumIdx_congr_then_fold
    (fun ρ => B_b ρ - ... + ...)      -- LHS function
    (fun ρ => - RiemannUp ... * g ...)  -- Main RHS function
    (fun ρ => g M ρ ρ r θ * (...))    -- Rho-core RHS function
    ?_  -- pointwise proof
```

## Questions

**Option A**: Should I use the simpler `sumIdx_congr` pattern instead?
```lean
have hb_plus := by
  classical
  rw [hb_pack]
  -- Fold RHS: - sumIdx (RiemannUp...) + sumIdx (rho_core...)
  rw [← sumIdx_add_distrib, ← h_rho_core_b]
  -- Reduce to pointwise
  refine sumIdx_congr ?_
  intro ρ
  -- Pointwise algebra here with simp + stable folds
  sorry
```

**Option B**: Should I update `sumIdx_congr_then_fold` to match your expected signature?

**Option C**: Is there a different lemma I should use that takes 3 functions?

## Current State

- File: `Riemann.lean`
- `hb_plus` helper: lines 8753-8959 (207 lines with current complex calc)
- `ha_plus` helper: lines 9176-9378 (207 lines, symmetric to hb_plus)
- Both helpers currently use `rw [hb_pack]` followed by complex calc chains
- Error count with current approach: 29 (baseline: 18, target: 17)

## Next Steps

Awaiting clarification on which pattern to use, then will:
1. Implement the pointwise pattern for `hb_plus`
2. Implement symmetrically for `ha_plus`
3. Verify `branches_sum` works with the new helpers
4. Build and confirm error count drops to 17

---

**Files ready for edit once pattern is confirmed**:
- `hb_plus` proof body (lines 8760-8959)
- `ha_plus` proof body (lines ~9180-9378)
