# Memo to JP: Pack Helpers Complete - Request for Regroup Lemma Guidance

**Date:** October 11, 2025
**From:** Claude Code (AI Agent)
**To:** JP (Junior Professor)
**Re:** Pack helpers implemented successfully - Need guidance on regroup lemmas

---

## Executive Summary

✅ **Pack helpers are complete!** Both `pack_right_slot_prod` and `pack_left_slot_prod` compile with 0 errors and 0 sorries using your Option C approach (explicit Or-branch proof terms).

**Commit:** `9f72dd4` - "feat(P5/GR): Complete pack helper lemmas with explicit proof terms"

**Next blocker:** Need guidance on implementing the regroup lemmas (`regroup_right_sum_to_RiemannUp_NEW` and `regroup_left_sum_to_RiemannUp_NEW`) to close the 6 remaining Section C sorries.

---

## What Was Completed

### 1. Wrapper Lemmas (Lines 5621-5666)

Implemented all 4 differentiability wrappers with Exterior hypotheses:

```lean
lemma g_differentiable_r_ext (M r θ : ℝ) (h_ext : Exterior M r θ) (i j : Idx) :
  DifferentiableAt_r (fun r θ => g M i j r θ) r θ

lemma g_differentiable_θ_ext (M r θ : ℝ) (h_ext : Exterior M r θ) (i j : Idx) :
  DifferentiableAt_θ (fun r θ => g M i j r θ) r θ

lemma Γtot_differentiable_r_ext_μθ (M r θ : ℝ) (h_ext : Exterior M r θ) (k a : Idx) :
  DifferentiableAt_r (fun r θ => Γtot M r θ k Idx.θ a) r θ

lemma Γtot_differentiable_θ_ext_μr (M r θ : ℝ) (h_ext : Exterior M r θ) (k a : Idx) :
  DifferentiableAt_θ (fun r θ => Γtot M r θ k Idx.r a) r θ
```

**Key implementation details:**
- Case analysis on all 16 metric components (diagonal uses existing lemmas, off-diagonal = 0)
- Special handling for Γ^r_{θθ} = -r (linear, uses `fun_prop`)
- Special handling for Γ^θ_{rθ} = 1/r (uses `DifferentiableAt.div` with `Exterior.r_ne_zero`)
- All other Christoffel cases: constant or zero

### 2. Pack Helper Lemmas (Lines 5681-5780)

Both lemmas implemented with your exact structure:

```lean
lemma pack_right_slot_prod (M r θ : ℝ) (h_ext : Exterior M r θ) (a b k : Idx) :
  (dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a) r θ) * g M k b r θ
- (dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a) r θ) * g M k b r θ
+ Γtot M r θ k Idx.θ a * dCoord Idx.r (fun r θ => g M k b r θ) r θ
- Γtot M r θ k Idx.r a * dCoord Idx.θ (fun r θ => g M k b r θ) r θ
=
  dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a * g M k b r θ) r θ
- dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a * g M k b r θ) r θ
```

**Proof pattern:**
```lean
have Hr : ... := by
  simpa using (dCoord_mul_of_diff Idx.r ...
    (Or.inl (Γtot_differentiable_r_ext_μθ ...))
    (Or.inl (g_differentiable_r_ext ...))
    (Or.inr (by decide : Idx.r ≠ Idx.θ))
    (Or.inr (by decide : Idx.r ≠ Idx.θ)))

have Hθ : ... := by
  simpa using (dCoord_mul_of_diff Idx.θ ...)

have step1 : ... = ... := by ring
rw [step1, Hr, Hθ]
```

**Result:** Clean compilation, no sorries needed!

---

## Current Status

**Build:** ✅ 3078 jobs, 0 errors
**Sorries:** 6 (original Section C only - lines 2641, 3148, 3221, 3258, 3267, 3282)

**Files modified:**
- `GR/Riemann.lean`: +162 lines, -7 lines

**What works:**
- All 4 wrapper lemmas handle all index combinations correctly
- Both pack helpers apply product rule correctly
- Build is completely clean

---

## What We Need Next

### Critical Path to Close Section C

```
pack_right_slot_prod ✅ ──┐
                          ├──> regroup_right_sum_to_RiemannUp_NEW ❓
pack_left_slot_prod  ✅ ──┤
                          └──> regroup_left_sum_to_RiemannUp_NEW ❓
                                  │
                                  ├──> ricci_identity_on_g_rθ_ext (sorry at 2641)
                                  ├──> Riemann_swap_a_b_ext (sorries at 3148, 3221)
                                  └──> Riemann_swap_a_b (sorries at 3258, 3267, 3282)
```

### Question 1: Do You Have Regroup Lemma Templates?

In your last message you said:
> "If you'd like, I can sketch the regroup_right_sum_to_RiemannUp_NEW skeleton next"

**Request:** Could you provide:
1. The signature for `regroup_right_sum_to_RiemannUp_NEW`
2. The signature for `regroup_left_sum_to_RiemannUp_NEW`
3. Proof structure/skeleton for one of them (I can adapt for the other)

**What I expect:** These lemmas should:
- Take a sum over index `k` of the 4-term expression
- Use `pack_right_slot_prod` (or `pack_left`) to rewrite as difference of products
- Swap sum and dCoord somehow
- Arrive at RiemannUp expansion

**What I don't know:**
- Exact form of the sum-swap lemmas needed
- Whether we need additional infrastructure for summing over indices
- How to connect to the existing `RiemannUp` definition

### Question 2: Should I Try to Infer the Structure?

I can attempt to reverse-engineer the regroup lemmas from the usage sites:

**Option A:** Wait for your skeleton (safest, fastest if you have it ready)
**Option B:** Infer from usage and implement myself (slower, might need corrections)

**My recommendation:** Option A, since you already have the design in mind and it will save debugging time.

---

## Technical Notes for Implementation

### Tools Available

From the pack helper experience, we now have:
- ✅ Product rule via `dCoord_mul_of_diff` with explicit Or branches
- ✅ Differentiability infrastructure for g and Γ on Exterior
- ✅ `ring` tactic for algebraic rearrangements
- ✅ `Finset.sum` infrastructure (already used in file)

### Potential Infrastructure Gaps

Things that might be needed for regroup lemmas:
- **Sum-derivative interchange:** `dCoord μ (∑ k, f k) = ∑ k, dCoord μ (f k)` (might exist already?)
- **Sum manipulation lemmas:** Splitting sums, reindexing
- **Connection to RiemannUp:** Exact formula that the sum should equal

### Where Are We Going?

Looking at line 2641 (first sorry):
```lean
lemma ricci_identity_on_g_rθ_ext (M r θ : ℝ) (h_ext : Exterior M r θ) :
  (∑ k : Idx, RiemannUp M r θ k Idx.r k Idx.θ) = 0 := by
  sorry
```

So we need to prove that the sum of Riemann components equals 0. The regroup lemmas presumably help by reorganizing this sum into a form that cancels.

---

## Recommendation

**Immediate next step:** Wait for your regroup lemma skeleton.

**Rationale:**
1. Pack helpers took multiple tactical iterations to get right
2. The regroup lemmas are the "main event" of Section C
3. Your design is already proven to work structurally
4. Saves 2-4 hours of trial-and-error implementation

**Alternative:** If you prefer me to attempt inference, I can:
1. Study the 6 sorry sites in detail
2. Look at how RiemannUp is defined and used
3. Draft candidate signatures and ask for validation
4. Implement with sorries for unclear parts

**ETA if you provide skeleton:** 2-4 hours (implementation + testing)
**ETA if I infer:** 4-8 hours (exploration + multiple iterations + corrections)

---

## Summary

✅ **Completed:** Pack helpers fully implemented with 0 sorries
❓ **Blocked on:** Regroup lemma structure/skeleton
⏳ **Waiting for:** Your guidance on next implementation step

**Build status:** Clean (0 errors, 6 original sorries)
**Ready to proceed:** As soon as regroup structure is provided

Thank you for the excellent pack helper guidance - the explicit Or-branch approach worked perfectly!

---

**Prepared by:** Claude Code (AI Agent)
**Session:** Pack Helper Completion + Section C Planning
**Commit:** 9f72dd4
**Status:** 🟡 Awaiting regroup lemma guidance
