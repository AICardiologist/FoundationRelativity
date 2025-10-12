# Pack Helper Tactical Issue - Oct 11, 2025

**Status:** Implemented with 4 sorries, build compiles cleanly

---

## Summary

I've implemented both `pack_right_slot_prod` and `pack_left_slot_prod` following JP's structural template, but hit tactical issues with the product rule that prevent the lemmas from closing. The mathematical content is correct - it's purely a product rule application - but JP's suggested tactic `simp [dCoord_r, deriv_mul]` doesn't work as stated.

---

## What I Implemented

### Location
Lines 5614-5670 in Riemann.lean (before `end RicciInfrastructure`)

### Code Structure (pack_right_slot_prod)

```lean
lemma pack_right_slot_prod
    (M r θ : ℝ) (a b k : Idx) :
  (dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a) r θ) * g M k b r θ
- (dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a) r θ) * g M k b r θ
+ Γtot M r θ k Idx.θ a * dCoord Idx.r (fun r θ => g M k b r θ) r θ
- Γtot M r θ k Idx.r a * dCoord Idx.θ (fun r θ => g M k b r θ) r θ
=
  dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a * g M k b r θ) r θ
- dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a * g M k b r θ) r θ := by
  classical
  have Hr :
      dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a * g M k b r θ) r θ
        =
      dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a) r θ * g M k b r θ
      + Γtot M r θ k Idx.θ a * dCoord Idx.r (fun r θ => g M k b r θ) r θ := by
    -- TODO: JP suggested simp [dCoord_r, deriv_mul] but deriv_mul needs differentiability hyps
    sorry
  have Hθ :
      dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a * g M k b r θ) r θ
        =
      dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a) r θ * g M k b r θ
      + Γtot M r θ k Idx.r a * dCoord Idx.θ (fun r θ => g M k b r θ) r θ := by
    -- TODO: Same as Hr - product rule needs right approach
    sorry
  -- TODO: Combine Hr and Hθ to get final form
  rw [Hr, Hθ]
  ring
```

**pack_left_slot_prod** has identical structure (just swaps `a` ↔ `b` in the metric argument positions).

---

## The Tactical Issue

### What JP Suggested

JP's Message 3 said:
> "Replace your sorry in pack_right_slot_prod with the first snippet."

And provided:
```lean
have Hr :
    dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a * g M k b r θ) r θ
      =
    dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a) r θ * g M k b r θ
    + Γtot M r θ k Idx.θ a * dCoord Idx.r (fun r θ => g M k b r θ) r θ := by
  simp [dCoord_r, deriv_mul]
```

### What Actually Happened

**Attempt 1:** `simp [dCoord_r, deriv_mul]`
- **Result:** Unsolved goals at lines 5628, 5634 (for pack_right)
- **Why it failed:** `deriv_mul` from mathlib has the signature:
  ```lean
  theorem deriv_mul (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
      deriv (fun y => f y * g y) x = deriv f x * g x + f x * deriv g x
  ```
  So it requires differentiability hypotheses that simp can't auto-discharge.

**Attempt 2:** `simp [dCoord_r, deriv_mul]; ring`
- **Result:** Still unsolved goals
- **Why it failed:** Adding `ring` doesn't help if `deriv_mul` can't even be applied

**Attempt 3:** `rw [deriv_mul]` after `simp only [dCoord_r]`
- **Result:** "Did not find an occurrence of the pattern"
- **Why it failed:** After unfolding `dCoord_r`, we have:
  ```lean
  deriv (fun s => Γtot M s θ k Idx.θ a * g M k b s θ) r
  ```
  But `deriv_mul` expects `deriv (f * g) x`, not `deriv (fun s => ...) x` (lambda abstraction prevents matching).

---

## Mathematical Content

The lemmas are mathematically trivial - just the product rule:
- ∂_r(Γ·g) = (∂_r Γ)·g + Γ·(∂_r g)
- ∂_θ(Γ·g) = (∂_θ Γ)·g + Γ·(∂_θ g)

The issue is purely tactical: getting Lean to recognize and apply the product rule in the specific context of `dCoord` (which wraps `deriv` with a lambda abstraction).

---

## What I Tried

1. ❌ Direct `simp [dCoord_r, deriv_mul]` - JP's suggestion, but doesn't work
2. ❌ Adding `ring` after simp - still can't apply deriv_mul
3. ❌ Manual `rw [deriv_mul]` after unfolding - pattern mismatch
4. ❌ Using `conv` to manipulate lambda before applying deriv_mul - complex and error-prone
5. ✅ **Using `sorry` placeholders** - allows build to proceed

---

## Current Status

**Build:** ✅ Compiles cleanly (3078 jobs)
**Sorries:**
- pack_right_slot_prod: 2 sorries (Hr, Hθ)
- pack_left_slot_prod: 2 sorries (Hr, Hθ)
- **Total: 4 new sorries + 6 original = 10 sorries**

**Location:**
- Line 5614: pack_right_slot_prod
- Line 5643: pack_left_slot_prod

---

## Questions for JP

### Q1: Product Rule Tactic
Your suggestion was `simp [dCoord_r, deriv_mul]`, but `deriv_mul` requires differentiability hypotheses that simp doesn't discharge. What should I use instead?

**Options I can think of:**
- **A:** Prove differentiability lemmas for `Γtot` and `g` as prerequisites?
- **B:** Use a different product rule lemma that's unconditional?
- **C:** Manually expand with calc chains (but that's 20+ line proofs for "trivial" lemmas)?
- **D:** Something else entirely?

### Q2: dCoord Definition
`dCoord_r` unfolds to `deriv (fun s => F s θ) r`, which is a lambda abstraction. `deriv_mul` expects `deriv (f * g) x` without the lambda. Should I:
- Use a different unfolding strategy?
- Apply deriv_mul at a different point in the proof?
- Use functional extensionality first?

### Q3: Proceed or Pause?
Given that the pack helpers are micro infrastructure for the main regroup lemmas, should I:
- **A:** Continue implementing the regroup lemmas with pack helpers as sorries (they'll work structurally, just not proven)?
- **B:** Pause and get the pack helpers working first?

---

## Impact on Section C

**Critical Path:**
```
pack_right_slot_prod (sorry) ──┐
                                ├──> regroup_right_sum_to_RiemannUp_NEW
pack_left_slot_prod (sorry) ───┤
                                └──> regroup_left_sum_to_RiemannUp_NEW
```

If we can't fix the pack helpers, the regroup lemmas will depend on sorries. Alternatively, I could inline the product rule directly in the regroup lemmas, but that would be messy and repeat code.

---

## Recommendation

**Immediate Action:** Request JP's tactical fix for the product rule application.

**Alternative:** If the tactical issue is deep, consider adding differentiability infrastructure lemmas:
```lean
lemma Γtot_differentiable_r (M r θ : ℝ) (i j k : Idx) :
    DifferentiableAt ℝ (fun s => Γtot M s θ i j k) r := sorry

lemma g_differentiable_r (M r θ : ℝ) (i j : Idx) :
    DifferentiableAt ℝ (fun s => g M i j s θ) r := sorry
```

Then use them explicitly:
```lean
have Hr := by
  rw [dCoord_r, dCoord_r, dCoord_r]
  rw [deriv_mul (Γtot_differentiable_r M r θ k Idx.θ a) (g_differentiable_r M r θ k b)]
  simp
```

But this seems like overkill for "trivial" product rule lemmas.

---

## Build Verification

**Command:** `lake build Papers.P5_GeneralRelativity.GR.Riemann`

**Output:**
```
warning: Papers/P5_GeneralRelativity/GR/Riemann.lean:5614:6: declaration uses 'sorry'
warning: Papers/P5_GeneralRelativity/GR/Riemann.lean:5643:6: declaration uses 'sorry'
Build completed successfully (3078 jobs).
```

**Errors:** 0 ✅
**Sorries:** 10 (4 new in pack helpers + 6 original)

---

## Next Steps (Pending JP's Response)

**If JP provides working tactics:**
1. Replace sorries in pack_right_slot_prod (Hr, Hθ)
2. Replace sorries in pack_left_slot_prod (Hr, Hθ)
3. Verify build still clean
4. Proceed to regroup lemma implementations

**If tactical fix requires infrastructure:**
1. Add differentiability lemmas for Γtot and g
2. Update pack helpers to use them explicitly
3. Proceed as above

**If we proceed with sorries:**
1. Implement regroup_right_sum_to_RiemannUp_NEW using pack_right_slot_prod (with sorry)
2. Implement regroup_left_sum_to_RiemannUp_NEW using pack_left_slot_prod (with sorry)
3. Test structural integration
4. Revisit pack helpers later with JP's help

---

**Prepared by:** Claude Code (AI Agent)
**Date:** October 11, 2025
**Status:** Pack helpers implemented with sorries, awaiting tactical guidance

**Bottom Line:** The structure is correct and build-clean. Just need the right tactic to apply the product rule in the context of dCoord's lambda abstraction. Once that's resolved, the 4 sorries should close quickly (they're mathematically trivial).
