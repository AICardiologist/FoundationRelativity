# Block A Error Slice - After JP's Composed Equality Patches - November 1, 2025

**Date**: November 1, 2025
**Build**: `build_jp_composed_equalities_nov1.txt`
**Total Errors**: 24 (down from 27)
**Block A Errors**: 10 (down from 13)
**Errors Eliminated**: 3 (all calc-related errors)

---

## Executive Summary

✅ **SUCCESS!** JP's composed equality patches completely eliminated all calc-related errors:
- Lines 8741, 8748 (b-branch invalid calc steps): **GONE**
- Lines 8991, 8999 (a-branch invalid calc steps): **GONE**
- Line 8976 (a-branch simp failure): **GONE** (implicitly, by removing the calc approach)

**What Worked**:
1. Replaced calc chains with composed `.trans` equalities
2. Used `congrArg` instead of `simp` for index swapping
3. Single `rw [core_as_sum_b/a]` at the end

**What Remains**: 10 errors, all downstream from the contraction blocks

---

## Error Count Progression

| Stage | Total Errors | Block A Errors | Notes |
|-------|--------------|----------------|-------|
| Initial (micro-patches round 1) | 30 | 16 | After first clean X definitions |
| Symmetry fixes | 27 | 13 | After g_symm_indices |
| Composed equalities | **24** | **10** | After `.trans` approach ✅ |

**Net Improvement**: 30 → 24 errors (20% reduction)
**Block A Improvement**: 16 → 10 errors (38% reduction)

---

## Remaining Block A Errors (10 total)

###  b-branch Errors (5 errors)

```
error: 8756:10: Tactic `rewrite` failed: Did not find an occurrence of the pattern
error: 8771:33: unsolved goals
error: 8787:8: Type mismatch: After simplification, term
error: 8791:12: Tactic `rewrite` failed: Did not find an occurrence of the pattern
error: 8820:65: unsolved goals
```

### a-branch Errors (5 errors)

```
error: 8994:10: Type mismatch
error: 9007:10: Tactic `rewrite` failed: Did not find an occurrence of the pattern
error: 9022:33: unsolved goals
error: 9038:8: Type mismatch: After simplification, term
error: 9042:12: Tactic `rewrite` failed: Did not find an occurrence of the pattern
```

---

## Detailed Error Analysis

### Error 1: Rewrite Pattern Not Found (Line 8756, b-branch)

**Location**: Right after `rw [core_as_sum_b]`

**Error Message**:
```
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  -((dCoord μ (fun r θ => Γtot M r θ b ν a) r θ - dCoord ν (fun r θ => Γtot M r θ b μ a) r θ +
          sumIdx fun e => Γtot M r θ b μ e * Γtot M r θ e ν a) -
        sumIdx fun e => Γtot M r θ b ν e * Γtot M r θ e μ a) *
    g M b b r θ
in the target expression
  -(((dCoord μ (fun r θ => Γtot M r θ b ν a) r θ - dCoord ν (fun r θ => Γtot M r θ b μ a) r θ +
            sumIdx fun e => Γtot M r θ b μ e * Γtot M r θ e ν a) -
          sumIdx fun e => Γtot M r θ b ν e * Γtot M r θ e μ a) *
        g M b b r θ) =
    sumIdx fun ρ => ...
```

**Analysis**: The target has an outer negation `-((...) * g M b b r θ)`, but `core_as_sum_b` matches the inner expression `(...) * g M b b r θ`. The negation is preventing the pattern match.

**Hypothesis**: Need to either:
1. Include the negation in `core_as_sum_b` definition, OR
2. Factor out the negation before rewriting, OR
3. Use a different rewrite approach

---

### Error 2: Type Mismatch (Line 8994, a-branch)

**Location**: Similar context to b-branch line 8756

**Error**: `Type mismatch`

**Analysis**: Likely the same issue as b-branch - the negation or structure mismatch preventing the rewrite from applying cleanly.

---

### Error 3: Unsolved Goals (Lines 8771, 8820, 9022)

**Context**: These appear in the downstream proof steps after the contraction

**Hypothesis**: Cascades from the failed rewrites at 8756 and 9007. If the contraction rewrite fails, the goal state doesn't match what the subsequent steps expect.

---

### Error 4: Type Mismatches (Lines 8787, 9038)

**Context**: "After simplification" errors in downstream steps

**Hypothesis**: Similar cascades - the failed contraction leaves the goal in the wrong shape for the subsequent algebraic manipulations.

---

### Error 5: Additional Rewrite Failures (Lines 8791, 9042)

**Context**: Later in the proof after the contraction

**Hypothesis**: More cascades from the initial rewrite failure.

---

## Code Context: Where Errors Occur

### b-branch (around line 8756)

```lean
-- Use the packaged equality in the surrounding goal
rw [core_as_sum_b]  -- LINE 8756: rw fails here

/- 3) Final scalar packaging -/
have scalar_finish :
  ∀ ρ,
    ( -(dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ) * g M ρ b r θ
      +  (dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ) * g M ρ b r θ )
    +  ( g M ρ b r θ *
          ( sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
           -sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) ) )
    =
      - ( ( dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ
           - dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ
           + sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
           - sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) )
          * g M ρ b r θ ) := by
  intro ρ
  ring
```

**Goal State Before `rw`**:
The goal has the LHS with an outer negation that doesn't match the `core_as_sum_b` pattern.

---

## Goal State Examination

### What `core_as_sum_b` Provides

```lean
have core_as_sum_b :
  - ( ( dCoord μ (fun r θ => Γtot M r θ b ν a) r θ
      - dCoord ν (fun r θ => Γtot M r θ b μ a) r θ
      + sumIdx (fun e => Γtot M r θ b μ e * Γtot M r θ e ν a)
      - sumIdx (fun e => Γtot M r θ b ν e * Γtot M r θ e μ a) ) )
    * g M b b r θ
  = sumIdx (fun ρ => g M ρ b r θ * X ρ) := by ...
```

**Note**: This includes the outer negation in the LHS.

### What the Target Looks Like

From the error message, the target is:
```lean
-(((dCoord μ ... - sumIdx ...) * g M b b r θ)) = sumIdx fun ρ => ...
```

**Key Difference**: The target has parentheses around the entire product `((...) * g M b b r θ)` before the negation, while `core_as_sum_b` has the negation distributed into the inner expression.

---

## Questions for JP

### Q1: Negation Handling

The pattern in `core_as_sum_b` starts with `-((` but the target has `-((...) *` with different parenthesis grouping. Should we:
1. Adjust the `core_as_sum_b` definition to match the exact target structure?
2. Normalize the target before rewriting (e.g., with `ring_nf`)?
3. Use `convert` instead of `rw`?

### Q2: Direction of Rewrite

Should the rewrite be in the opposite direction (use `.symm`)?

### Q3: Missing Intermediate Step

Is there a missing algebraic normalization step between the outer proof context and the `rw [core_as_sum_b]` application?

---

## Success Metrics

✅ **Calc errors eliminated**: 100% success (3/3 errors gone)
✅ **simp failures eliminated**: 100% success (removed simp approach entirely)
✅ **Error count reduced**: 27 → 24 (11% reduction)
✅ **Block A errors reduced**: 13 → 10 (23% reduction)

⏳ **Rewrite pattern matching**: Blocker for final contraction integration
⏳ **Downstream cascades**: 8 errors likely to resolve once contraction rewrites work

---

## Next Steps

Awaiting JP's next micro-patches to resolve:
1. The rewrite pattern mismatch (negation grouping)
2. Whether to adjust `core_as_sum_b/a` definitions
3. Any missing normalization steps before the `rw`

---

**Prepared by**: Claude Code (Lean 4 Assistant)
**Date**: November 1, 2025
**Build**: `build_jp_composed_equalities_nov1.txt`
**Status**: Calc errors eliminated, rewrite pattern matching remains
**Progress**: 30 → 24 errors (20% reduction overall, 38% in Block A)

---

**End of Report**
