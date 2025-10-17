# Follow-up: Infinite Loop Issue in Steps 4-7
## Date: October 17, 2025
## To: Senior Professor
## From: Research Team

---

## Issue Summary

Attempted to implement your fallback calc approach for Steps 4-7, but encountered an **infinite loop** when using `simp_rw [mul_sumIdx_distrib]` in the have statements for Fubini application.

**Build Status**: ✅ Passes (with sorry at line 1645)
**Blocker**: Tactical infinite loop prevents completion

---

## What Was Attempted

### Attempt 1: Kitchen Sink `simp only`

```lean
simp only [
  sumIdx_map_sub,
  mul_sub, mul_add,
  sumIdx_add_distrib,
  mul_sumIdx_distrib,
  sumIdx_swap  -- Caused loop warning
]
```

**Result**: Lean warned "Possibly looping simp theorem: `sumIdx_swap`" and hit max recursion depth.

### Attempt 2: Your Fallback Calc Approach

Following your recommendation to use `have` statements:

```lean
have hC : sumIdx (fun ρ => g M β ρ r θ * sumIdx (fun lam => Γtot M r θ ρ Idx.r lam * Γtot M r θ lam Idx.θ a))
  = sumIdx (fun lam => sumIdx (fun ρ => g M β ρ r θ * (Γtot M r θ ρ Idx.r lam * Γtot M r θ lam Idx.θ a))) := by
  simp_rw [mul_sumIdx_distrib]  -- HANGS HERE
  rw [sumIdx_swap]
```

**Result**: Build hangs indefinitely at `simp_rw [mul_sumIdx_distrib]`. Had to kill the process.

---

## Root Cause Analysis

The lemma `mul_sumIdx_distrib` is defined as:

```lean
lemma mul_sumIdx_distrib (c : ℝ) (f : Idx → ℝ) :
  c * sumIdx f = sumIdx (fun k => c * f k)
```

When used with `simp_rw`, Lean appears to:
1. Rewrite `g * sumIdx (...)` to `sumIdx (fun k => g * (...))`
2. See another `sumIdx` inside and try to rewrite recursively
3. Create an infinite rewrite loop

The issue is that `mul_sumIdx_distrib` is a `@[simp]` lemma (or being used as one), and `simp_rw` applies it recursively to nested structures.

---

## Diagnostic Information

**Line**: 1661 in original attempt
**Context**: Inside `have` statement within calc block
**Pattern**:
- LHS: `g M β ρ r θ * sumIdx (fun lam => Γtot M r θ ρ Idx.r lam * Γtot M r θ lam Idx.θ a)`
- Target: `sumIdx (fun lam => g M β ρ r θ * (Γtot M r θ ρ Idx.r lam * Γtot M r θ lam Idx.θ a))`

**Infrastructure Lemma** (line 1362):
```lean
/-- Left distribution: c * (Σk f k) = Σk (c * f k). Matches Finset.mul_sum.
    This is an alias for mul_sumIdx with standardized naming. -/
lemma mul_sumIdx_distrib (c : ℝ) (f : Idx → ℝ) :
  c * sumIdx f = sumIdx (fun k => c * f k) := by
  unfold sumIdx; rw [Finset.mul_sum]
```

---

## Questions for SP

### Q1: Non-looping Alternative to `simp_rw`?

Is there a tactic that applies `mul_sumIdx_distrib` **exactly once** without recursing into nested sums?

Options we considered:
- `rw [mul_sumIdx_distrib]` - Doesn't work (pattern matching fails in complex context)
- `erw [mul_sumIdx_distrib]` - Haven't tried yet
- `conv` with explicit navigation - Tried but couldn't find correct path after simp
- Custom helper lemma matching exact pattern?

### Q2: Should `mul_sumIdx_distrib` be Non-simp?

Is the issue that `mul_sumIdx_distrib` shouldn't be a `@[simp]` lemma? Should we:
1. Remove `@[simp]` attribute if present?
2. Create a non-simp variant for manual application?
3. Use `simp only` with explicit exclusion: `simp only [mul_sumIdx_distrib, -mul_sumIdx_distrib]`? (paradoxical but sometimes works)

### Q3: Specialized Helper Lemma?

Would it be cleaner to prove a specialized lemma for this exact pattern?

```lean
lemma sumIdx_mul_sumIdx_swap (g : Idx → ℝ) (f : Idx → Idx → ℝ) :
  sumIdx (fun ρ => g ρ * sumIdx (fun lam => f ρ lam))
  = sumIdx (fun lam => sumIdx (fun ρ => g ρ * f ρ lam)) := by
  simp_rw [mul_sumIdx_distrib]  -- If this doesn't loop
  rw [sumIdx_swap]
```

Then use: `rw [sumIdx_mul_sumIdx_swap]` in the main proof?

---

## Current Workaround

For now, Steps 4-7 is documented with a sorry (line 1645):

```lean
-- Issue: simp_rw [mul_sumIdx_distrib] creates infinite loop
-- Need: Either non-looping tactic sequence or specialized helper lemma
sorry
```

This allows:
- ✅ Build to pass
- ✅ Progress on Step 8 (which depends on Steps 4-7 structure)
- ✅ Clear documentation of the blocker

---

## Impact

**Phase 3 Status**:
- Steps 1-3: ✅ Complete
- Steps 4-7: ⏳ Sorry (line 1645) - infinite loop blocker
- Step 8: ⏳ Sorry (line 1667) - depends on metric compatibility

**Overall**: ~75% mathematically complete, 2 tactical blockers

---

## Request

Please advise on:
1. Correct tactic to apply `mul_sumIdx_distrib` once without recursion
2. Whether to create specialized helper lemma
3. Any Lean 4 idiom for "apply this lemma exactly once to the outermost occurrence"

**Priority**: Medium - not blocking other work, but needed to complete Phase 3.

---

**Prepared by**: Research Team
**Date**: October 17, 2025
**Build Status**: ✅ Passes (3078 jobs)
**File**: `Riemann.lean` lines 1628-1645
