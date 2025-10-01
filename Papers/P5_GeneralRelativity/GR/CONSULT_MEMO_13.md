# Consultation Memo: Tactical Guidance Request - Final Push to TRUE LEVEL 3

**To:** Professor
**From:** AI Development Team  
**Date:** October 1, 2025 (Continued Session)
**Re:** Both Paths Implemented, Tactical Blockers Identified

---

## Executive Summary

**Status:** ✅ Build PASSING (0 errors) | 7 sorries (5 original + 2 C3 stubs)

**Progress:**
- ✅ Path B (discharge_diff): Enhanced per MEMORANDUM, proof strategy validated
- ✅ Path A (C3): Infrastructure in place, stubs documented
- ⚠️ Both paths need tactical guidance for final completion

**Request:** Tactical patterns for nested hypothesis discharge OR second-order differentiability

---

## Question 1: Path B - Nested Hypothesis Discharge

**Context:** After `rw [dCoord_sumIdx]` + `funext k`, goal is:
```
k : Idx
⊢ DifferentiableAt_r (fun r θ => Γtot M r θ k c a) r θ ∨ μ ≠ Idx.r
```

**Issue:** Enhanced `discharge_diff` has `| { apply Γtot_differentiable_r <;> try assumption }` but doesn't match.

**Question:** How to handle hypothesis discharge in nested `∀` contexts after `funext`?

---

## Question 2: Path A - Second Derivative Differentiability

**Goal:** Prove `DifferentiableAt ℝ (deriv (fun r' => f M r')) r` where `f M r = 1 - 2*M/r`, `r ≠ 0`

**Math:** f''(r) = -4M/r³ exists (trivial)

**Attempts:**
1. ContDiffAt → don't know extraction lemma
2. Direct deriv → type inference issues

**Question:** Standard mathlib pattern for proving second-order differentiability of rational functions?

---

## Documentation

- TACTICAL_STATUS_DISCHARGE_DIFF.md (full Path B analysis)
- SESSION_PROGRESS_SUMMARY.md (complete overview)
- Riemann.lean lines 597-642 (enhanced tactic)
- Riemann.lean lines 289-319 (C3 stubs)

**Git:** 8eb34a1, build passing

---

## Impact

**Path A unblocks:** 2 sorries (dCoord_g_differentiable_r/θ)
**Path B unblocks:** Main theorem (alternation_dC_eq_Riem)
**Both unblock:** TRUE LEVEL 3 ✅

Standing by for guidance.
