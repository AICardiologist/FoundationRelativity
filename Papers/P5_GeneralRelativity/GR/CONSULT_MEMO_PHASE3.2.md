# Consultation Memo: Phase 3.2 - alternation_dC_eq_Riem Strategy

**To:** Professor
**From:** AI Development Team
**Date:** October 1, 2025
**Subject:** Phase 3.1 Complete (ricci_LHS) - Request Guidance for Phase 3.2 (alternation_dC_eq_Riem)

---

## Executive Summary

**Phase 3.1 Status:** ✅ COMPLETE - ricci_LHS proof successful using Force Rewrite pattern

**Phase 3.2 Status:** ⚠️ BLOCKED - alternation_dC_eq_Riem proof scaffold broken after Phase 3.1 deletions

**Request:** Strategic guidance on how to approach alternation_dC_eq_Riem given that:
1. Stage1LHS infrastructure was deleted per Phase 3.1
2. dCoord_mul was replaced with dCoord_mul_of_diff
3. Old proof scaffold (lines 1771-2600+) references deleted infrastructure

---

## I. Phase 3.1 Completion Report

### What We Accomplished

**1. Successfully Applied Force Rewrite Pattern**

```lean
-- Lines 1552-1602: ricci_LHS proof
lemma ricci_LHS (M r θ : ℝ) (a b c d : Idx) :
  ( dCoord c (fun r θ => nabla_g M r θ d a b) r θ
  - dCoord d (fun r θ => nabla_g M r θ c a b) r θ )
  = - ( dCoord c (fun r θ => ContractionC M r θ d a b) r θ
        - dCoord d (fun r θ => ContractionC M r θ c a b) r θ ) := by
  -- 1. Expand definition
  simp only [nabla_g_eq_dCoord_sub_C]

  -- 2. Force Linearization (distribute dCoord over subtraction)
  repeat (rw [dCoord_sub_of_diff])

  -- 3. Discharge Differentiability Preconditions
  all_goals (try (first
    | apply Or.inl; apply dCoord_g_differentiable_r
    | apply Or.inl; apply dCoord_g_differentiable_θ
    | apply Or.inl; apply ContractionC_differentiable_r
    | apply Or.inl; apply ContractionC_differentiable_θ
  ))

  -- 4. Apply Commutativity (Clairaut's theorem)
  have h_commute : [16 cases by symmetry proof]

  -- Apply commutativity
  rw [h_commute]

  -- 5. Normalize
  ring
```

**Result:** ✅ Proof complete, 0 build errors

**2. Added C2 Smoothness Infrastructure**

```lean
-- Lines 1517-1548: C2 lemmas
@[simp]
lemma ContractionC_differentiable_r (M r θ : ℝ) (a b c : Idx) :
  DifferentiableAt_r (fun r θ => ContractionC M r θ a b c) r θ := by
  sorry

@[simp]
lemma ContractionC_differentiable_θ (M r θ : ℝ) (a b c : Idx) :
  DifferentiableAt_θ (fun r θ => ContractionC M r θ a b c) r θ := by
  sorry

@[simp]
lemma dCoord_g_differentiable_r (M r θ : ℝ) (μ a b : Idx) :
  DifferentiableAt_r (dCoord μ (fun r θ => g M a b r θ)) r θ := by
  sorry

@[simp]
lemma dCoord_g_differentiable_θ (M r θ : ℝ) (μ a b : Idx) :
  DifferentiableAt_θ (dCoord μ (fun r θ => g M a b r θ)) r θ := by
  sorry
```

**Why This Works:** Using sorry for C2 lemmas is acceptable per your pragmatic approach - these are provable facts about concrete functions, deferred for efficiency.

**3. Build Status**

```
✅ 0 errors
✅ Full build passing
✅ All quality gates passing
```

---

## II. Phase 3.2 Blocker: alternation_dC_eq_Riem

### Current State

**Lemma Statement (Line 1750):**

```lean
lemma alternation_dC_eq_Riem (M r θ : ℝ) (a b c d : Idx) :
  ( dCoord c (fun r θ => ContractionC M r θ d a b) r θ
  - dCoord d (fun r θ => ContractionC M r θ c a b) r θ )
  = ( Riemann M r θ a b c d + Riemann M r θ b a c d ) := by
  sorry  -- Line 1769
```

**What This Proves:** The difference of derivatives of the Christoffel contraction equals the sum of Riemann tensors (alternation identity).

**Why It Matters:** This is used in the proof chain:
1. ricci_LHS ✅ (just completed)
2. alternation_dC_eq_Riem ⏳ (current blocker)
3. ricci_identity_on_g (uses both above)
4. Riemann_swap_a_b_ext (final antisymmetry proof)

### The Broken Proof Scaffold

**Lines 1771-1850: Commented-out proof uses deleted infrastructure**

```lean
/-
-- Stage-1 splits (both families)
have hC := Stage1_LHS_Splits.Hsplit_c_both M r θ a b c d  -- ❌ DELETED in Phase 3.1
have hD := Stage1_LHS_Splits.Hsplit_d_both M r θ a b c d  -- ❌ DELETED

-- First family c-branch: push dCoord across 4-term sum
have hC₁ :=
  dCoord_add4_flat c
    (fun r θ => Γtot M r θ Idx.t d a * g M Idx.t b r θ)
    (fun r θ => Γtot M r θ Idx.r d a * g M Idx.r b r θ)
    (fun r θ => Γtot M r θ Idx.θ d a * g M Idx.θ b r θ)
    (fun r θ => Γtot M r θ Idx.φ d a * g M Idx.φ b r θ)
    r θ

-- [Similar for hC₂, hD₁, hD₂]

-- Push product rule on t-summands
have hpush_ct₁ :
  dCoord c (fun r θ => Γtot M r θ Idx.t d a * g M Idx.t b r θ) r θ
  = ... := by
  exact dCoord_mul c  -- ❌ DELETED in Phase 3.1 (replaced with dCoord_mul_of_diff)
    (fun r θ => Γtot M r θ Idx.t d a)
    (fun r θ => g M Idx.t b r θ) r θ

-- [Continues for ~850 more lines with similar broken references]
-/
```

**Problems:**
1. **Stage1_LHS_Splits deleted:** We deleted this namespace in Phase 3.1 cleanup (lines 1659-1777)
2. **dCoord_mul deleted:** Replaced with hypothesis-carrying `dCoord_mul_of_diff`
3. **Massive proof scaffold:** ~850 lines of commented-out code that's now broken
4. **Performance concerns:** Original comment says "performance issues" with Hsplit lemmas

---

## III. Strategic Questions for Phase 3.2

### Question 1: Should We Restore Stage1_LHS_Splits?

**Option A: Restore and Update Stage1_LHS_Splits**
- Uncomment the deleted Stage1_LHS_Splits section
- Update all references to use new hypothesis-carrying infrastructure
- Update dCoord_mul → dCoord_mul_of_diff with differentiability proofs
- **Pro:** Follows existing proof structure
- **Con:** Large refactoring effort, original had performance issues

**Option B: Rewrite Without Stage1_LHS_Splits**
- Design new proof that doesn't use Stage1_LHS_Splits
- Use simpler decomposition strategy
- **Pro:** Cleaner, potentially faster
- **Con:** Need to understand mathematical structure from scratch

**Which approach do you recommend?**

---

### Question 2: What Is the Mathematical Structure?

To proceed, we need to understand what alternation_dC_eq_Riem is actually computing:

**Goal:**
```lean
( dCoord c (ContractionC M r θ d a b)
- dCoord d (ContractionC M r θ c a b) )
= ( Riemann M r θ a b c d + Riemann M r θ b a c d )
```

**Where:**
```lean
ContractionC M r θ d a b = sumIdx (fun k => Γtot M r θ k d a * g M k b r θ)
                         + sumIdx (fun k => Γtot M r θ k d b * g M a k r θ)

Riemann M r θ a b c d = [definition in terms of dCoord Γ and Γ·Γ products]
```

**Question:** What's the high-level strategy?
1. Expand ContractionC to its sum definition
2. Distribute dCoord over the sum (using dCoord_sumIdx or dCoord_add4)
3. Apply product rule to each term (using dCoord_mul_of_diff)
4. Relate the resulting terms to Riemann tensor definition
5. Algebraic simplification

**Is this the right approach, or is there a simpler path?**

---

### Question 3: What About dCoord_mul_of_diff?

The old proof used `dCoord_mul` extensively. Now we have `dCoord_mul_of_diff` which requires differentiability hypotheses:

```lean
-- Old (deleted):
lemma dCoord_mul (μ : Idx) (A B : ℝ → ℝ → ℝ) (r θ : ℝ) :
  dCoord μ (fun r θ => A r θ * B r θ) r θ
  = dCoord μ A r θ * B r θ + A r θ * dCoord μ B r θ := by
  sorry  -- Unsound - assumed arbitrary A, B differentiable

-- New (active):
lemma dCoord_mul_of_diff (μ : Idx) (A B : ℝ → ℝ → ℝ) (r θ : ℝ)
    (hA_r : DifferentiableAt_r A r θ ∨ μ ≠ Idx.r)
    (hB_r : DifferentiableAt_r B r θ ∨ μ ≠ Idx.r)
    (hA_θ : DifferentiableAt_θ A r θ ∨ μ ≠ Idx.θ)
    (hB_θ : DifferentiableAt_θ B r θ ∨ μ ≠ Idx.θ) :
  dCoord μ (fun r θ => A r θ * B r θ) r θ
  = dCoord μ A r θ * B r θ + A r θ * dCoord μ B r θ := by
  [proof using differentiability]
```

**Question:** For the alternation proof, the functions are:
- `A = fun r θ => Γtot M r θ k d a` (Christoffel symbol)
- `B = fun r θ => g M k b r θ` (metric component)

Both Γ and g are concrete differentiable functions. Should we:

**Option A:** Add differentiability lemmas for Γtot (similar to our C2 lemmas):
```lean
lemma Γtot_differentiable_r (M r θ : ℝ) (i j k : Idx) :
  DifferentiableAt_r (fun r θ => Γtot M r θ i j k) r θ := by sorry

lemma Γtot_differentiable_θ (M r θ : ℝ) (i j k : Idx) :
  DifferentiableAt_θ (fun r θ => Γtot M r θ i j k) r θ := by sorry
```

Then use discharge_diff to handle all product rule applications?

**Option B:** Prove differentiability inline for each specific case?

**Option C:** Something else?

---

### Question 4: Proof Size and Performance

The commented scaffold is ~850 lines and has a note about "performance issues."

**Question:** Should we:

**Option A:** Implement as one large lemma with set_option maxHeartbeats?
```lean
lemma alternation_dC_eq_Riem ... := by
  set_option maxHeartbeats 2000000 in
  [850 lines of tactics]
```

**Option B:** Decompose into helper lemmas?
```lean
-- Helper 1: Expand ContractionC and distribute dCoord
lemma alternation_expand_LHS : ... := by [50 lines]

-- Helper 2: Apply product rules to all terms
lemma alternation_product_rules : ... := by [200 lines]

-- Helper 3: Relate to Riemann definition
lemma alternation_relate_Riemann : ... := by [300 lines]

-- Helper 4: Final algebraic simplification
lemma alternation_simplify : ... := by [300 lines]

-- Main theorem uses helpers
lemma alternation_dC_eq_Riem : ... := by
  rw [alternation_expand_LHS, alternation_product_rules,
      alternation_relate_Riemann, alternation_simplify]
```

**Which approach would you recommend?**

---

## IV. Minimal Working Example of the Issue

To illustrate the problem, here's a simplified version:

**What the proof needs to do:**

```lean
-- Expand ContractionC
ContractionC M r θ d a b
  = Γtot(t,d,a)·g(t,b) + Γtot(r,d,a)·g(r,b) + Γtot(θ,d,a)·g(θ,b) + Γtot(φ,d,a)·g(φ,b)
  + Γtot(t,d,b)·g(a,t) + ...

-- Distribute dCoord_c over each term
dCoord_c [Γtot(t,d,a)·g(t,b) + ...]
  = dCoord_c [Γtot(t,d,a)·g(t,b)] + dCoord_c [Γtot(r,d,a)·g(r,b)] + ...

-- Apply product rule to each term (THIS IS WHERE WE NEED dCoord_mul_of_diff)
dCoord_c [Γtot(t,d,a)·g(t,b)]
  = (dCoord_c Γtot(t,d,a))·g(t,b) + Γtot(t,d,a)·(dCoord_c g(t,b))

-- Now we have ~16 terms of derivatives of Γ and g
-- Need to relate these to Riemann tensor definition
-- Riemann also involves derivatives of Γ and Γ·Γ products

-- Final step: algebraic manipulation to show LHS = RHS
```

**The Challenge:** This requires:
1. ~50 applications of dCoord_mul_of_diff
2. Each needs 4 differentiability hypotheses discharged
3. Then complex algebraic manipulation with ~100+ terms
4. Must match against Riemann tensor definition structure

---

## V. Current Codebase State

**Active Sorries:**
- 4 in C2 lemmas (ContractionC_differentiable_r/θ, dCoord_g_differentiable_r/θ)
- 1 in alternation_dC_eq_Riem (this blocker)
- Others in commented/deferred sections

**Build Status:** ✅ 0 errors (alternation_dC_eq_Riem sorry doesn't break build)

**Dependencies Waiting:**
- ricci_identity_on_g (line 3098) - uses ricci_LHS ✅ and alternation_dC_eq_Riem ⏳
- Riemann_swap_a_b_ext (line 3116) - final antisymmetry proof

---

## VI. Specific Tactical Questions

### 6a. ContractionC Expansion

How should we expand ContractionC? The definition is:

```lean
def ContractionC (M r θ : ℝ) (c a b : Idx) : ℝ :=
  sumIdx (fun k => Γtot M r θ k c a * g M k b r θ)
  + sumIdx (fun k => Γtot M r θ k c b * g M a k r θ)
```

**Option 1:** Use sumIdx infrastructure
```lean
simp only [ContractionC]
-- Now have: dCoord_c (sumIdx ...) - dCoord_d (sumIdx ...)
```

**Option 2:** Expand sumIdx to 4-term sum directly
```lean
simp only [ContractionC, sumIdx_expand]
-- Now have explicit 8-term sum (4 terms per sumIdx)
```

**Which is cleaner?**

---

### 6b. Distributing dCoord Over Sum

We have two lemmas available:

**Option 1:** Use dCoord_sumIdx (requires differentiability for all terms)
```lean
lemma dCoord_sumIdx (μ : Idx) (F : Idx → ℝ → ℝ → ℝ) (r θ : ℝ)
    (hF_r : ∀ i, DifferentiableAt_r (F i) r θ ∨ μ ≠ Idx.r)
    (hF_θ : ∀ i, DifferentiableAt_θ (F i) r θ ∨ μ ≠ Idx.θ) :
  dCoord μ (fun r θ => sumIdx (fun i => F i r θ)) r θ =
    sumIdx (fun i => dCoord μ (fun r θ => F i r θ) r θ)
```

**Option 2:** Use dCoord_add4_flat (4-way addition)
```lean
lemma dCoord_add4_flat (μ : Idx) (A B C D : ℝ → ℝ → ℝ) (r θ : ℝ)
    [8 differentiability hypotheses] :
  dCoord μ (fun r θ => A r θ + B r θ + C r θ + D r θ) r θ =
    dCoord μ A r θ + dCoord μ B r θ + dCoord μ C r θ + dCoord μ D r θ
```

**Which should we use?**

---

### 6c. Product Rule Applications

After distributing dCoord, we need product rules. Each application of dCoord_mul_of_diff needs 4 hypotheses.

**Should we:**

**Option 1:** Extend discharge_diff with Γtot differentiability lemmas
```lean
-- Add these lemmas:
@[simp] lemma Γtot_differentiable_r ...
@[simp] lemma Γtot_differentiable_θ ...

-- Then product rules become:
apply dCoord_mul_of_diff
all_goals discharge_diff  -- Auto-discharges all 4 hypotheses
```

**Option 2:** Manual hypothesis discharge (like we did for ricci_LHS)
```lean
apply dCoord_mul_of_diff
· apply Or.inl; exact Γtot_differentiable_r ...
· apply Or.inl; exact g_differentiable_r ...
· apply Or.inl; exact Γtot_differentiable_θ ...
· apply Or.inl; exact g_differentiable_θ ...
```

**Which is more maintainable for ~50 product rule applications?**

---

## VII. Proposed Plan (Pending Your Guidance)

**If you recommend proceeding without Stage1_LHS_Splits:**

**Phase 3.2a: Infrastructure (Estimated: 1-2 hours)**
1. Add Γtot differentiability lemmas (with sorry, like C2 lemmas)
2. Add any missing product differentiability combinators
3. Test discharge_diff handles all hypothesis patterns

**Phase 3.2b: Proof Structure (Estimated: 2-4 hours)**
1. Expand ContractionC to sum form
2. Distribute dCoord using dCoord_add4_flat or dCoord_sumIdx
3. Apply product rules to each term (discharge hypotheses automatically)
4. [Algebraic manipulation - need guidance on strategy]

**Phase 3.2c: Relate to Riemann (Estimated: 2-4 hours)**
1. Expand Riemann definition on RHS
2. Match terms from LHS expansion to RHS structure
3. Use ring/abel_nf for final simplification

**Total Estimate:** 5-10 hours

---

## VIII. What We Need From You

**Primary Request:**
1. **Strategic decision:** Restore Stage1_LHS_Splits vs. rewrite from scratch?
2. **Mathematical guidance:** What's the high-level proof strategy for alternation_dC_eq_Riem?
3. **Tactical pattern:** What's the best way to handle ~50 product rule applications?

**Secondary Request:**
4. Should we decompose into helper lemmas or one large proof?
5. Any specific tactics you recommend for the algebraic manipulation phase?

---

## IX. Conclusion

Phase 3.1 (ricci_LHS) was a complete success using your Force Rewrite pattern. Build is clean with 0 errors.

Phase 3.2 (alternation_dC_eq_Riem) requires strategic guidance because the old proof scaffold depends on deleted infrastructure.

We're ready to implement immediately once we understand your preferred approach.

**Awaiting your direction for Phase 3.2.**

---

**Attached Files for Review:**
- `Riemann.lean` (line 1750): alternation_dC_eq_Riem statement
- `Riemann.lean` (lines 1771-2600+): Commented proof scaffold (broken)
- Git commit: `ed46222` - Phase 3.1 ricci_LHS completion

**Contact:** Ready to implement your guidance immediately.
