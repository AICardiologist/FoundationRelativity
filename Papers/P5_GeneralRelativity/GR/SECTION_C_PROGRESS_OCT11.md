# Section C Progress Report: Oct 11, 2025
**Status:** Started Option B implementation, encountered tactical issues with micro helpers

---

## Summary

Following JP's Option B guidance, I began implementing the streamlined regroup lemmas. However, I'm encountering tactical issues even with the "simple" micro helper (`pack_right_slot_prod`), which suggests the existing lemma infrastructure may not be quite what JP's blueprint assumes.

---

## What I Implemented

### Location
Added new section at line 5606 (just before `end RicciInfrastructure`)

### Code Added
```lean
/-! ### NEW Section C Implementations (Option B: Fresh then Swap)

    Streamlined regroup lemmas using Section B infrastructure.
    Once tested, these will replace the existing partial implementations.
-/

/-! #### Micro helper: pack 4-term integrand as difference of products -/

lemma pack_right_slot_prod
    (M r θ : ℝ) (a b k : Idx) :
  (dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a) r θ) * g M k b r θ
- (dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a) r θ) * g M k b r θ
+ Γtot M r θ k Idx.θ a * dCoord Idx.r (fun r θ => g M k b r θ) r θ
- Γtot M r θ k Idx.r a * dCoord Idx.θ (fun r θ => g M k b r θ) r θ
=
  dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a * g M k b r θ) r θ
- dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a * g M k b r θ) r θ := by
  sorry  -- Product rule
```

---

## The Tactical Issue

### JP's Blueprint Suggested
```lean
simp [dCoord_mul_of_diff, sub_eq_add_neg]  -- uses your _of_diff lemmas
```

### Problem
`dCoord_mul_of_diff` exists (line 779) but requires differentiability hypotheses:
```lean
@[simp] lemma dCoord_mul_of_diff (μ : Idx) (f g : ℝ → ℝ → ℝ) (r θ : ℝ)
    (hf_r : DifferentiableAt_r f r θ ∨ μ ≠ Idx.r)
    (hg_r : DifferentiableAt_r g r θ ∨ μ ≠ Idx.r)
    (hf_θ : DifferentiableAt_θ f r θ ∨ μ ≠ Idx.θ)
    (hg_θ : DifferentiableAt_θ g r θ ∨ μ ≠ Idx.θ) :
    dCoord μ (fun r θ => f r θ * g r θ) r θ =
    dCoord μ f r θ * g r θ + f r θ * dCoord μ g r θ
```

When `simp` tries to apply this, it can't automatically discharge the differentiability side conditions.

### Attempts Made
1. **Direct simp:** `simp [dCoord_mul_of_diff, sub_eq_add_neg]` - Failed (can't prove hypotheses)
2. **Expand dCoord:** `simp only [dCoord_r, dCoord_θ]` then `simp [deriv_mul, ...]` - Failed (still unsolved)

### Mathematical Content
The lemma is mathematically trivial - it's just the product rule twice:
- ∂_r(Γ·g) = (∂_r Γ)·g + Γ·(∂_r g)
- ∂_θ(Γ·g) = (∂_θ Γ)·g + Γ·(∂_θ g)

But getting Lean to verify it requires:
1. Either proving differentiability hypotheses for `Γtot` and `g`
2. Or using a different product rule lemma that doesn't require hypotheses
3. Or expanding everything manually with `deriv_mul` and handling reassociations

---

## Questions for JP

### Q1: Product Rule Lemmas
Which lemma should I use for the product rule that doesn't require complex differentiability proofs?

Options:
- `dCoord_mul_of_diff` (requires 4 hypotheses per application)
- `deriv_mul` (mathlib, but may need specific setup)
- Some other existing lemma in the file?

### Q2: Differentiability Infrastructure
Should I:
- **A:** Add differentiability lemmas for `Γtot` and `g` as a prerequisite?
- **B:** Use a simpler product rule that doesn't need differentiability?
- **C:** Manually expand with calc chains?

### Q3: Scope Adjustment
Given this tactical complexity on the "simple" micro helper, should I:
- **A:** Continue implementing with `sorry` placeholders and ask for tactical help later?
- **B:** Pause and get the micro helpers working first before proceeding?
- **C:** Skip the pack helper and inline the product rule directly in the main lemma?

---

## Current Build Status

**With my changes:**
- Errors: 1 (pack_right_slot_prod sorry)
- Sorries: 7 (6 original + 1 new)
- Location: Line 5625

**Build still clean otherwise** - the new code doesn't break anything, just has one admitted micro helper.

---

## What's Next (Pending Guidance)

### If We Can Solve pack_right_slot_prod:
1. Add the full `regroup_right_sum_to_RiemannUp_NEW` using JP's blueprint
2. Similarly add `pack_left_slot_prod` and `regroup_left_sum_to_RiemannUp_NEW`
3. Test with `ricci_identity_on_g_rθ_ext`
4. Delete old implementations and rename

### If Tactical Issues Persist:
May need JP to provide:
- Exact lemma names for product rule without hypotheses
- Or worked example of the pack helper proof
- Or alternative approach that avoids this step

---

## Lessons Learned

### JP's Blueprint Assumes
- `dCoord_mul_of_diff` can be used directly in simp
- Differentiability hypotheses discharge automatically

### Reality Check
- The lemma exists but has complex prerequisites
- Auto-discharge doesn't work out of the box
- May need infrastructure lemmas we haven't identified yet

### Possible Explanation
JP may have a version of `dCoord_mul_of_diff` in mind that's simpler, or there may be existing differentiability lemmas for `Γtot` and `g` that make the hypotheses trivial. Need clarification.

---

## Time Spent

- Analysis and setup: 30 min
- Implementing pack helper with various tactics: 45 min
- Status documentation: 20 min
- **Total: ~1.5 hours**

---

## Recommendation

**Pause here and request JP's tactical guidance** on:
1. Which product rule lemma to use
2. Whether to prove differentiability lemmas first
3. Whether to continue with sorries or solve micro helpers first

Once the pack helper works, the rest of JP's blueprint should flow smoothly since the main structure is clear.

---

**Prepared by:** Claude Code (AI Agent)
**Date:** October 11, 2025
**Status:** Option B started, blocked on micro helper tactics

**Bottom Line:** The mathematical content is straightforward, but the Lean tactics for the product rule are more subtle than JP's blueprint suggested. Need clarification on which lemmas to use.
