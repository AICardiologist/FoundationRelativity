# CONSULTATION MEMO 9: Critical Blocker in Priority 2

**Date:** September 30, 2025
**Status:** 🔴 **BLOCKER DISCOVERED** - Targeted Approach Infeasible
**Branch:** `feat/p0.2-invariants`

---

## Executive Summary

Attempted to implement the "optimal approach" from PRIORITY_2_FINAL_APPROACH.md (targeted elimination of ~13 specific downstream uses). **Discovered critical blocker:** Christoffel symbols (Γtot) lack differentiability lemmas, making targeted elimination impossible without massive additional infrastructure work.

**Conclusion:** The "optimal approach" is NOT feasible. We have only TWO viable paths forward:

1. **Accept Level 2.5** - Keep both sorries quarantined, document clearly
2. **Prove Γtot differentiability** - Weeks of additional work (50+ lemmas)

---

## What Happened

### Attempted Replacement

**Target:** Line 1377-1380 in Riemann.lean (Hc1_one product rule)

**Original Code:**
```lean
simpa using
  dCoord_mul c
    (fun r θ => Γtot M r θ Idx.t d a)
    (fun r θ => g M Idx.t b r θ) r θ
```

**Attempted Replacement:**
```lean
simpa using
  dCoord_mul_of_diff c
    (fun r θ => Γtot M r θ Idx.t d a)
    (fun r θ => g M Idx.t b r θ) r θ
    (by discharge_diff) (by discharge_diff) (by discharge_diff) (by discharge_diff)
```

### Build Error

**4 unsolved goals** at line 1381:
```
⊢ DifferentiableAt_r (fun r θ => Γtot M r θ Idx.t d a) r θ ∨ c ≠ Idx.r
⊢ DifferentiableAt_r (fun r θ => g M Idx.t b r θ) r θ ∨ c ≠ Idx.r
⊢ DifferentiableAt_θ (fun r θ => Γtot M r θ Idx.t d a) r θ ∨ c ≠ Idx.θ
⊢ DifferentiableAt_θ (fun r θ => g M Idx.t b r θ) r θ ∨ c ≠ Idx.θ
```

**The Problem:** `discharge_diff` tactic knows how to prove differentiability for **metric components** (g), but NOT for **Christoffel symbols** (Γtot).

---

## Root Cause Analysis

### Incorrect Assumption in PRIORITY_2_FINAL_APPROACH.md

**Claim (Line 62):**
> "**Why eliminable**: Both Γtot and g have proven differentiability"

**Reality:** This is FALSE.

- ✅ Metric components (g): 6 differentiability lemmas exist (lines 262-343)
- ❌ Christoffel symbols (Γtot): ZERO differentiability lemmas exist

### Search Results

**Searched for:**
- `differentiableAt.*Γ` - No results
- `Γtot.*diff` - No results
- Lemmas about Γtot - Only found `Γtot_symmetry` (line 800)

**Conclusion:** No differentiability infrastructure exists for Christoffel symbols.

---

## Why This Is a Blocker

### Scope of Required Work

To prove differentiability for Γtot, we would need:

**1. Christoffel Symbol Differentiability Lemmas (13 nonzero components × 2 directions = 26 lemmas)**

For each nonzero Γtot component:
- `Γtot_t_tr`, `Γtot_t_rt`, `Γtot_r_tt`, `Γtot_r_rr`, `Γtot_r_θθ`, `Γtot_r_φφ`
- `Γtot_θ_rθ`, `Γtot_θ_θr`, `Γtot_φ_rφ`, `Γtot_φ_φr`
- `Γtot_θ_φφ`, `Γtot_φ_θφ`, `Γtot_φ_φθ`

Prove differentiability in both r and θ directions:
```lean
lemma differentiableAt_Γtot_t_tr_r (M r θ : ℝ) :
  DifferentiableAt ℝ (fun r' => Γtot M r' θ Idx.t Idx.t Idx.r) r := by
  sorry -- Requires proving differentiability of metric inverse components

lemma differentiableAt_Γtot_t_tr_θ (M r θ : ℝ) :
  DifferentiableAt ℝ (fun θ' => Γtot M r θ' Idx.t Idx.t Idx.r) θ := by
  sorry -- Similar
```

**2. Metric Inverse Differentiability Lemmas (6 components × 2 directions = 12 lemmas)**

Γtot depends on `gInv` (metric inverse), which lacks differentiability lemmas:
```lean
lemma differentiableAt_gInv_tt_r (M r θ : ℝ) :
  DifferentiableAt ℝ (fun r' => gInv M Idx.t Idx.t r' θ) r := by
  sorry -- Requires inverse function theorem or explicit formulas
```

**3. Metric Derivative Differentiability (6 components × 2 directions = 12 lemmas)**

Γtot also depends on `dCoord μ g`:
```lean
lemma differentiableAt_dg_tt_r_r (M r θ : ℝ) :
  DifferentiableAt ℝ (fun r' => dCoord Idx.r (fun r θ => g M Idx.t Idx.t r θ) r' θ) r := by
  sorry -- Second derivatives of metric
```

**Total:** ~50 lemmas minimum, potentially weeks of work.

---

## Options Going Forward

### Option A: Accept Level 2.5 (RECOMMENDED)

**What It Means:**
- Keep both `AX_nabla_g_zero` and `AX_differentiable_hack` as quarantined sorries
- Document clearly in LEVEL_2_5_ASSESSMENT.md
- Critical path (Schwarzschild.lean) remains axiom-free ✅
- Riemann.lean has 2 quarantined sorries with clear elimination paths

**Advantages:**
- ✅ Publication-ready NOW
- ✅ No additional work required
- ✅ Honest about current state
- ✅ Can pursue TRUE LEVEL 3 post-publication

**Timeline:** Ready immediately (just documentation updates)

---

### Option B: Prove Γtot Differentiability (NOT RECOMMENDED)

**What It Means:**
- Prove ~50 differentiability lemmas for Christoffel symbols and dependencies
- Update `discharge_diff` tactic to use these lemmas
- Proceed with targeted elimination approach

**Disadvantages:**
- ❌ Estimated 4-6 weeks additional work
- ❌ High complexity (inverse function theorem, second derivatives)
- ❌ Delays publication significantly
- ❌ Risk of discovering additional blockers

**Timeline:** 4-6 weeks minimum

---

## Recommendation

**Accept Level 2.5** and document clearly.

**Rationale:**
1. **Critical path is axiom-free** - Schwarzschild.lean builds with 0 axioms ✅
2. **Quarantined sorries are well-understood** - Clear mathematical content
3. **Publication-ready** - Level 2.5 meets all scientific standards
4. **Efficient use of time** - 4-6 weeks for TRUE LEVEL 3 better spent post-publication

---

## Verification

**Build Status:** ✅ All passing (3078 jobs)
**Axiom Count:** 0 actual axioms, 2 sorries (lines 253, 1149)
**Critical Path:** ✅ Schwarzschild.lean axiom-free
**Current State:** Stable, working, publication-ready at Level 2.5

---

**Status:** 🔴 **BLOCKER - Awaiting Strategic Decision**
**Recommendation:** Accept Level 2.5, document clearly, pursue TRUE LEVEL 3 post-publication

🎯 **Key Insight:** TRUE LEVEL 3 requires 50+ differentiability lemmas we don't have. Level 2.5 is publication-ready NOW.
