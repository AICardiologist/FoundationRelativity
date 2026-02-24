# Consultation Memo: Path Selection for Final 5 Sorries

**To:** Professor
**From:** AI Development Team
**Date:** October 1, 2025
**Subject:** Request Tactical Guidance - Two Paths to TRUE LEVEL 3

---

## Executive Summary

**Current Status:** ✅ Build Passing (0 errors) | 5 sorries remaining (67% reduction from 15)

**Progress Since Last Memo:**
- ✅ Hypothesis Management COMPLETE (all 10 C1/C2 lemmas FULLY PROVEN)
- ✅ Investigated both remaining paths to TRUE LEVEL 3
- ⚠️ Both paths require advanced Lean/mathlib expertise beyond current capability

**Request:** Tactical guidance on preferred path and specific techniques

---

## Part 1: What We've Accomplished

### 1.1 Major Milestone: 10 Lemmas Fully Proven (160 cases)

**C1 Smoothness (128 cases, 0 sorries):**
- `Γtot_differentiable_r/θ` - All 64 cases per direction ✅
- `g_differentiable_r/θ` - All 16 cases per direction ✅

**C2 Smoothness (0 sorries):**
- `ContractionC_differentiable_r/θ` - FULLY PROVEN ✅

**Infrastructure (0 sorries):**
- `ricci_LHS` - FULLY PROVEN ✅
- `ricci_identity_on_g`, `Riemann_*_ext` - Updated with hypotheses ✅

**Git:** Committed as "feat(P5/GR): Complete Hypothesis Management cascade - 10 lemmas proven"

### 1.2 Investigation Results

**Path A: C3 Smoothness Base Facts**
- Status: ⚠️ ATTEMPTED, hit mathlib complexity
- Created stub: `differentiableAt_deriv_f` (line 290)
- Blocker: Need correct `deriv` lemma applications or `ContDiff` patterns

**Path B: dCoord_ContractionC_expanded**
- Status: ✅ STRATEGY VALIDATED, tactical blocker documented
- Successfully constructed `hF_r` and `hF_θ` (30+ lines working)
- Blocker: `discharge_diff` tactic doesn't pass hypothesis parameters
- Documentation: `DCCOORD_CONTRACTION_APPROACH.md` (full analysis)

---

## Part 2: The Two Paths Forward

### PATH A: C3 Smoothness (Prove Twice-Differentiability)

**Questions for Professor:**
1. Should we use `ContDiff` instead of iterating `DifferentiableAt`?
2. Does mathlib have lemmas like `ContDiff.inv` or `ContDiff.pow` that handle this cleanly?
3. What's the standard pattern for proving rational functions are C^n?
4. Minimal example: How to prove `fun r => 1/r` is C² for r ≠ 0?

**Impact:** Unblocks 2 sorries (dCoord_g_differentiable_r/θ)

---

### PATH B: Enhanced discharge_diff Tactic

**Questions for Professor:**
1. Is the proposed macro fix correct (apply Or.inl; apply C1_lemma; try assumption × 3)?
2. How to systematically handle `Or.inl` application?
3. Pattern for testing tactic changes without breaking existing usages?

**Impact:** Unblocks critical path (dCoord_ContractionC_expanded → alternation_dC_eq_Riem)

---

## Part 3: Our Recommendation

**We recommend PATH B first** because:
1. It's on the critical path to the main theorem
2. Infrastructure improvement benefits future work  
3. Tactical guidance more actionable than mathlib deep-dive

But we defer to your expertise on which path is better.

---

## Part 4: Specific Requests

See full memo body in CONSULT_MEMO_11.md for:
- Detailed sorry-by-sorry analysis
- Attempted code and error messages
- Step-by-step tactical requests

---

**Attachments:**
1. `DCCOORD_CONTRACTION_APPROACH.md` - Full PATH B analysis
2. `CONTINUATION_SESSION_SUMMARY.md` - PATH A attempt
3. `SESSION_STATUS.md` - Current state
4. `Riemann.lean` - Build passing, 5 sorries documented

**Contact:** Awaiting path selection and tactical guidance.
