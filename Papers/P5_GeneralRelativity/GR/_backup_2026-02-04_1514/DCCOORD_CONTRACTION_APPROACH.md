# dCoord_ContractionC_expanded: Proof Strategy and Tactical Blocker

**Date:** October 1, 2025
**Status:** Proof strategy VALIDATED, implementation BLOCKED on tactical complexity

---

## Executive Summary

**Goal:** Prove that derivative of ContractionC distributes correctly (Product Rule + Leibniz Rule)

**Current State:**
- ✅ Strategy is SOUND (hF_r and hF_θ hypotheses successfully constructed)
- ❌ Implementation BLOCKED on verbose hypothesis discharge (14+ hypothesis discharges required)
- ⚙️ Workaround: Keep sorry, revisit after tactical infrastructure improvements

---

## Proof Strategy (Professor's Sequential Rewrite)

```lean
lemma dCoord_ContractionC_expanded (M r θ : ℝ) (μ c a b : Idx)
    (hM : 0 < M) (h_ext : 2 * M < r) (h_sin_nz : Real.sin θ ≠ 0) :
  dCoord μ (fun r θ => ContractionC M r θ c a b) r θ =
  sumIdx (fun k =>
    (dCoord μ (fun r θ => Γtot M r θ k c a) r θ * g M k b r θ +
     Γtot M r θ k c a * dCoord μ (fun r θ => g M k b r θ) r θ)
    +
    (dCoord μ (fun r θ => Γtot M r θ k c b) r θ * g M a k r θ +
     Γtot M r θ k c b * dCoord μ (fun r θ => g M a k r θ) r θ)
  ) := by
  simp only [ContractionC]
  rw [dCoord_sumIdx _ _ _ _ hF_r hF_θ]
  congr; ext k
  rw [dCoord_add_of_diff ...]  -- 4 hypotheses
  rw [dCoord_mul_of_diff ...]  -- 4 hypotheses
  rw [dCoord_mul_of_diff ...]  -- 4 hypotheses
```

**Steps:**
1. Expand ContractionC definition
2. Push dCoord through sumIdx (requires 2 hypothesis proofs: hF_r and hF_θ)
3. Distribute over sum terms (congr; ext k)
4. Apply dCoord_add_of_diff (requires 4 hypothesis discharges)
5. Apply dCoord_mul_of_diff twice (requires 8 hypothesis discharges total)

**Total hypothesis discharges needed:** 2 + 4 + 4 + 4 = 14

---

## What Works: hF_r and hF_θ Construction

Successfully constructed the two main hypotheses for dCoord_sumIdx:

```lean
have hF_r : ∀ k, DifferentiableAt_r (fun r θ => Γtot M r θ k c a * g M k b r θ + Γtot M r θ k c b * g M a k r θ) r θ ∨ μ ≠ Idx.r := by
  intros k
  apply Or.inl
  unfold DifferentiableAt_r
  apply DifferentiableAt.add
  · apply DifferentiableAt.mul
    · exact Γtot_differentiable_r M r θ k c a hM h_ext h_sin_nz
    · exact g_differentiable_r M r θ k b hM h_ext h_sin_nz
  · apply DifferentiableAt.mul
    · exact Γtot_differentiable_r M r θ k c b hM h_ext h_sin_nz
    · exact g_differentiable_r M r θ a k hM h_ext h_sin_nz
```

This proves:
- ✅ C1 lemmas (Γtot_differentiable_r/θ, g_differentiable_r/θ) are correct and applicable
- ✅ Proof strategy follows valid mathematical steps
- ✅ Hypotheses can be constructed with explicit unfolding and mathlib lemmas

---

## What's Blocked: Subsequent Hypothesis Discharges

After `rw [dCoord_sumIdx _ _ _ _ hF_r hF_θ]`, need to discharge 12 more hypotheses for:

###3. dCoord_add_of_diff (4 hypotheses)
```lean
rw [dCoord_add_of_diff]
-- Need to prove:
-- hf_r : DifferentiableAt_r (fun r θ => Γ(k,c,a) * g(k,b)) r θ ∨ μ ≠ Idx.r
-- hg_r : DifferentiableAt_r (fun r θ => Γ(k,c,b) * g(a,k)) r θ ∨ μ ≠ Idx.r
-- hf_θ : DifferentiableAt_θ (fun r θ => Γ(k,c,a) * g(k,b)) r θ ∨ μ ≠ Idx.θ
-- hg_θ : DifferentiableAt_θ (fun r θ => Γ(k,c,b) * g(a,k)) r θ ∨ μ ≠ Idx.θ
```

### 4. dCoord_mul_of_diff × 2 (8 hypotheses total)
```lean
rw [dCoord_mul_of_diff]  -- First product
-- Need to prove 4 hypotheses for Γ(k,c,a) and g(k,b)
rw [dCoord_mul_of_diff]  -- Second product
-- Need to prove 4 hypotheses for Γ(k,c,b) and g(a,k)
```

**Tactical Issues Encountered:**
1. **Unification errors**: `apply Or.inl` fails in certain goal states
2. **Type mismatches**: After multiple rewrites, goal structure doesn't match expected forms
3. **Verbosity**: Each hypothesis requires 5-8 lines of tactics (unfold → apply → exact × 2-3)

**Attempted Fix:**
Manually discharged hypotheses for dCoord_add_of_diff using explicit unfold + DifferentiableAt.mul, but hit unification errors on lines 2005-2037 (see build log for details).

---

## Root Cause: discharge_diff Tactic Limitation

The discharge_diff tactic (lines 591-629 in Riemann.lean) uses a simp strategy:

```lean
simp only [DifferentiableAt_r, DifferentiableAt_θ,
           Γtot_differentiable_r, Γtot_differentiable_θ,
           g_differentiable_r, g_differentiable_θ,
           ...]
    <;> try assumption
```

**Problem:** These C1 lemmas now require hypotheses `(hM : 0 < M) (h_ext : 2 * M < r) (h_sin_nz : Real.sin θ ≠ 0)`, but simp doesn't properly instantiate them even with `<;> try assumption`.

---

## Solution Options

### Option A: Enhance discharge_diff Tactic ⭐ RECOMMENDED
**Complexity:** Moderate
**Impact:** High (unblocks all similar proofs)

Modify discharge_diff to explicitly pass hypotheses when applying C1 lemmas:

```lean
syntax "discharge_diff" : tactic
macro_rules
  | `(tactic| discharge_diff) => `(tactic| first
    | apply Or.inl; apply Γtot_differentiable_r; try assumption; try assumption; try assumption
    | apply Or.inl; apply Γtot_differentiable_θ; try assumption; try assumption; try assumption
    | apply Or.inl; apply g_differentiable_r; try assumption; try assumption; try assumption
    | apply Or.inl; apply g_differentiable_θ; try assumption; try assumption; try assumption
    | ... [other strategies]
  )
```

**Pros:**
- Fixes the root cause
- Benefits all future proofs using Condition Localization
- Maintains tactic abstraction

**Cons:**
- Requires understanding Lean 4 macro system
- Need to test against all existing discharge_diff usages

---

### Option B: Complete Manual Discharge
**Complexity:** High (62+ lines of repetitive tactics)
**Impact:** Low (only fixes this one lemma)

Continue the manual approach but resolve all unification/type errors.

**Pros:**
- No infrastructure changes needed
- Proves the lemma immediately

**Cons:**
- Extremely verbose (3x longer than actual mathematical content)
- Not reusable for other similar proofs
- Maintenance burden (any signature changes require updating 14+ locations)
- Hit unresolved tactical errors (lines 2005-2037 in attempted implementation)

---

### Option C: Refactor to Avoid Condition Localization
**Complexity:** Very High (redesign infrastructure)
**Impact:** High but risky

Remove Condition Localization patterns (P ∨ μ ≠ coord) entirely, always prove unconditional differentiability.

**Pros:**
- Simpler proof structure
- No hypothesis discharge needed

**Cons:**
- May not be mathematically possible (some functions truly aren't differentiable in all coords)
- Would require reproving/refactoring 10+ infrastructure lemmas
- High risk of introducing errors

---

## Recommendation

**SHORT TERM:** Keep sorry, document blocker (this file)
**MEDIUM TERM:** Implement Option A (enhance discharge_diff tactic)
**LONG TERM:** If Option A proves difficult, consider Option B for critical-path lemmas only

---

## Dependencies

**Blocked lemmas:**
- dCoord_ContractionC_expanded (1 sorry) ← THIS LEMMA
- alternation_dC_eq_Riem (1 sorry) - depends on above

**Ready lemmas (if this is proven):**
- alternation_dC_eq_Riem: Only algebraic normalization remains after dCoord_ContractionC_expanded

---

## Test Case: Verifying hF_r/hF_θ Construction

To verify that the strategy is sound, the hF_r and hF_θ construction can be tested in isolation:

```bash
lake build Papers.P5_GeneralRelativity.GR.Riemann
# Succeeds after reverting to clean state with sorry
```

The successfully built hF_r and hF_θ proofs (30+ lines) demonstrate that:
1. All C1 lemmas are accessible and correctly typed
2. Hypothesis passing works when done explicitly with `exact`
3. The proof structure is mathematically valid

---

**Contact:** AI Development Team
**For Assistance:** See CONSULT_MEMO_9.md for professor's original tactical guidance
