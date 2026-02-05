# discharge_diff Tactical Status Update

**Date:** October 1, 2025 (Continued Session)
**Build:** ✅ PASSING (3078 jobs)
**Sorries:** 6 (5 original + 1 C3 stub)

## Executive Summary

**Path B Enhancement: PARTIAL SUCCESS**

✅ **Completed:**
- Enhanced `discharge_diff` tactic per Professor's MEMORANDUM (lines 597-642)
- Strategy 2 implemented: Explicit `apply` with `<;> try assumption`
- Successfully replaced `simp only` approach with direct lemma application
- Base case hypothesis passing works correctly

⚠️ **Blocker Identified:**
- Nested hypothesis discharge still requires manual intervention
- `dCoord_ContractionC_expanded`: 2 hypotheses constructed successfully (hF_r, hF_θ), but remaining 12 hypotheses for nested product rules don't auto-discharge
- Issue: `discharge_diff` recursion doesn't handle all nested product/add combinations

## What Works

### Enhanced discharge_diff (Strategy 2)
```lean
-- Strategy 2: Base Facts (Explicit Application) - THE KEY ENHANCEMENT
| { apply Γtot_differentiable_r <;> try assumption }
| { apply Γtot_differentiable_θ <;> try assumption }
| { apply g_differentiable_r <;> try assumption }
| { apply g_differentiable_θ <;> try assumption }
```

**Validation:** Successfully discharges hypotheses in simple contexts where C1 lemmas apply directly.

### hF_r and hF_θ Construction (Validated)
```lean
have hF_r : ∀ k, DifferentiableAt_r (...) ∨ μ ≠ Idx.r := by
  intro k
  try { unfold DifferentiableAt_r }
  left
  apply DifferentiableAt.add <;> apply DifferentiableAt.mul
  · exact Γtot_differentiable_r M r θ k c a hM h_ext h_sin_nz
  · exact g_differentiable_r M r θ k b hM h_ext h_sin_nz
  · exact Γtot_differentiable_r M r θ k c b hM h_ext h_sin_nz
  · exact g_differentiable_r M r θ a k hM h_ext h_sin_nz
```

**Result:** Builds successfully, proves that C1 lemmas are correctly accessible and hypothesis passing works when done explicitly.

##What Doesn't Work

### Nested Product Rule Hypothesis Discharge

After `rw [dCoord_sumIdx _ _ _ _ hF_r hF_θ]` and `congr 1; funext k`, we need:

1. `rw [dCoord_add_of_diff]` → 4 hypotheses
2. `rw [dCoord_mul_of_diff]` (1st product) → 4 hypotheses
3. `rw [dCoord_mul_of_diff]` (2nd product) → 4 hypotheses

**Total:** 12 additional hypothesis discharges required

**Issue:** `discharge_diff` doesn't recursively apply in this nested context. Attempts to use:
- `<;> discharge_diff` → `assumption` fails
- `all_goals { first | exact Or.inl (...) }` → Type mismatches (tries wrong hypotheses for wrong goals)

### Root Cause Hypothesis

The `discharge_diff` tactic's `first` combinator with `left; discharge_diff` may not properly handle:
- Goals inside focused proof blocks (after `·`)
- Nested `all_goals` contexts
- Variable shadowing (lemma parameter `k` vs bound variable `k`)

## Options Forward

### Option 1: Further Tactic Refinement (RECOMMENDED by Professor)
- Investigate Lean 4 tactic scoping in nested contexts
- Add debugging: `trace` statements to see which strategies match
- Potentially split discharge_diff into `discharge_diff_base` and `discharge_diff_nested`

### Option 2: Manual 62-Line Discharge (FALLBACK)
- Explicitly discharge all 12 hypotheses with individual `exact Or.inl (...)` lines
- Pro: Guarantees proof completion
- Con: Verbose, not reusable, maintenance burden

### Option 3: Proceed with Path A First
- Implement ContDiffAt infrastructure (C3 smoothness)
- Unblock 2 sorries (dCoord_g_differentiable_r/θ)
- Return to dCoord_ContractionC_expanded with fresh perspective

## Recommendation

**IMMEDIATE:** Proceed with Path A (ContDiffAt infrastructure) as professor said it's "also mandatory"
**PARALLEL:** Request professor's tactical guidance on discharge_diff nested context handling
**FALLBACK:** Use manual discharge (Option 2) if tactical fix proves too complex

---

**Files Modified:**
- `Riemann.lean` lines 597-642: Enhanced discharge_diff tactic ✅
- `Riemann.lean` line 1987: dCoord_ContractionC_expanded (sorry with detailed blocker comment)

**Build Status:** ✅ PASSING
**Next Step:** Implement Path A (Bridge lemma + C3 base facts per Professor's MEMORANDUM)
