# Section C Status Report: Sorry Analysis
**Date:** October 11, 2025
**To:** Junior Professor
**From:** Claude Code (AI Agent)
**Status:** Section B complete, Section C analysis complete, awaiting guidance

---

## Executive Summary

After implementing Section B infrastructure (denominator shims, fold helpers, right-slot refolds), I analyzed the 6 remaining sorries to determine the best implementation strategy.

**Key Finding:** The sorries are more interdependent and partially-implemented than the initial templates suggested. Several have significant work-in-progress with internal sorries.

**Recommendation:** Request JP's guidance on whether to:
1. Complete the existing partial implementations
2. Start fresh using JP's templates
3. Focus on a specific entry point

---

## Detailed Sorry Analysis

### 1. Line 2635: `regroup_right_sum_to_RiemannUp`

**Status:** Partially implemented with **4 internal sorries** (lines 3138, 3204, 3245, 3258)

**Existing Approach:**
- Uses `compat_refold_r_kb` and `compat_refold_θ_kb` (left-slot refolds)
- Has H₁, H₂ lemmas for Fubini swaps
- Has `kk_refold_pointwise` using left-slot refolds
- Multiple calc chains in progress

**What's Missing:**
- Final closure of 4 internal proof steps
- Integration of the pieces into final equality

**JP's Template Difference:**
- JP's template suggests using **right-slot** refolds (`compat_refold_r_ak`, `compat_refold_θ_ak`)
- Existing code uses **left-slot** refolds
- May need to decide: continue existing approach vs. adopt JP's template

**Complexity:** High (600+ lines with nested lemmas)

---

### 2. Line 3142: `regroup_left_sum_to_RiemannUp`

**Status:** Partially implemented with **multiple internal steps** in progress

**Existing Approach:**
- Mirror structure of `regroup_right_sum`
- Uses left-slot compat rewrites
- Has distribution and Fubini swap logic

**What's Missing:**
- Similar to regroup_right, needs final closure

**JP's Guidance:**
> "Same shape as the right-slot proof, but use:
>  sumIdx_mul_g_left / sumIdx_mul_g_left_comm for the collapse,
>  compat_refold_r_kb / compat_refold_θ_kb for the refolds"

**Observation:** Existing code already uses this approach!

**Complexity:** High (mirror of regroup_right)

---

### 3. Line 3215: `ricci_identity_on_g_rθ_ext`

**Status:** Nearly complete! Only **1 final sorry** at line 3245

**Existing Approach (BAK8 style):**
```lean
simp only [nabla, nabla_g_shape]
-- Cancel pure ∂∂ g by commutativity
have Hcomm := dCoord_commute_for_g_all M r θ a b Idx.r Idx.θ
-- Use specialized distributors (no AC stalls)
have HrL := dCoord_r_sumIdx_Γθ_g_left_ext  M r θ h_ext a b
have HrR := dCoord_r_sumIdx_Γθ_g_right_ext M r θ h_ext a b
have HθL := dCoord_θ_sumIdx_Γr_g_left  M r θ a b
have HθR := dCoord_θ_sumIdx_Γr_g_right M r θ a b
-- Regroup using the two sum lemmas
have packR := regroup_right_sum_to_RiemannUp  M r θ h_ext a b
have packL := regroup_left_sum_to_RiemannUp   M r θ h_ext a b
-- TODO: Complete closure
sorry
```

**Dependency Chain:**
- Depends on `regroup_right_sum_to_RiemannUp` (line 2635)
- Depends on `regroup_left_sum_to_RiemannUp` (line 3142)

**Once upstream lemmas are complete, this should close quickly!**

**Complexity:** Low (given upstream lemmas) - just needs final tactical assembly

---

### 4. Line 3252: `ricci_identity_on_g`

**Status:** Sorry with comment about timeout issues

**Comment:**
```lean
/-- STATUS: This lemma times out even with 800k heartbeats during
    the normalization steps. The mathematical strategy is sound but
    requires a different tactical approach. Currently attempting
    case-by-case proof (see ricci_identity_on_g_r_θ test). -/
```

**JP's Guidance:**
Two routes:
1. Case-by-case (16 small lemmas, one per (c,d) pair)
2. Single lemma with `cases c; cases d` dispatch

**Recommendation:** Use JP's case-by-case approach after ext version works

**Complexity:** Medium (tedious but deterministic once ext version proven)

---

### 5. Line 3261: `Riemann_swap_a_b_ext`

**Status:** Simple sorry with clear dependency

**Comment:**
```lean
-- TODO: Depends on ricci_identity_on_g_rθ_ext which has 1 sorry remaining
-- Complete proof exists in bak8 and will be restored once upstream lemma is proven
sorry
```

**Dependency:** `ricci_identity_on_g_rθ_ext` (line 3215)

**Action:** Restore from bak8 once line 3215 is complete

**Complexity:** Low (already proven in bak8)

---

### 6. Line 3276: `Riemann_swap_a_b`

**Status:** Sorry with case-split structure sketched

**Comment:**
```lean
/-
TODO: Complete using Riemann_swap_a_b_ext once upstream lemmas are proven:
by_cases hM : 0 < M
· by_cases hr : 2 * M < r
  · exact Riemann_swap_a_b_ext M r θ ⟨hM, hr⟩ a b c d
  · sorry -- r ≤ 2M case
· sorry -- M ≤ 0 case
-/
```

**Dependency:** `Riemann_swap_a_b_ext` (line 3261)

**Action:** Complete case-split once ext version is proven

**Complexity:** Low (case-split dispatch to ext version)

---

## Dependency Graph

```
regroup_right_sum_to_RiemannUp (2635) ──┐
                                         ├──> ricci_identity_on_g_rθ_ext (3215)
regroup_left_sum_to_RiemannUp (3142) ───┘            │
                                                     ├──> Riemann_swap_a_b_ext (3261)
                                                     │            │
ricci_identity_on_g (3252) ──────────────────────────┘            │
(independent, case-by-case)                                      │
                                                                 ├──> Riemann_swap_a_b (3276)
                                                                 │    (general case-split)
```

**Critical Path:**
1. Complete `regroup_right_sum` and `regroup_left_sum` (the foundational lemmas)
2. Close `ricci_identity_on_g_rθ_ext` (uses the regroup lemmas)
3. Restore `Riemann_swap_a_b_ext` from bak8
4. Implement `Riemann_swap_a_b` case-split
5. Implement `ricci_identity_on_g` case-by-case (can be parallel)

---

## Key Questions for JP

### Q1: Existing vs. Template Approach

The existing `regroup_right_sum_to_RiemannUp` uses **left-slot** refolds, but JP's template suggests using **right-slot** refolds (the new `compat_refold_r_ak` and `compat_refold_θ_ak` we just added).

**Options:**
- **A:** Continue existing approach (complete the 4 internal sorries)
- **B:** Start fresh with JP's template using right-slot refolds
- **C:** Hybrid: keep structure, but swap to right-slot refolds where appropriate

**Recommendation needed:** Which path?

### Q2: Regroup Lemma Internal Structure

The existing regroup lemmas have extensive internal structure:
- H₁, H₂ lemmas for Fubini swaps
- kk_refold_pointwise with funext
- kk_refold_expanded with detailed calc chains
- Multiple intermediate `have` statements

JP's template is more streamlined (collapse → define F → refold → identify → calc).

**Question:** Should I:
- Trust the existing structure and just fill sorries?
- Simplify to JP's streamlined template?

### Q3: Priority Order

Given dependencies, what's the best order?

**Option A:** Bottom-up (complete regroup lemmas first)
- Pro: Unblocks everything downstream
- Con: Regroup lemmas are most complex

**Option B:** Top-down (complete simple sorries first for momentum)
- Pro: Quick wins on lines 3261, 3276
- Con: They depend on upstream lemmas anyway

**Recommendation needed:** Which strategy?

### Q4: Bak8 Restoration

Comment says "Complete proof exists in bak8 and will be restored once upstream lemma is proven."

**Questions:**
- Should I examine bak8 for guidance on completing the regroup lemmas?
- Are there other completed proofs in backups that could guide implementation?

---

## Section B Infrastructure Usage

The new infrastructure is ready to use:

### For Regroup Lemmas:
```lean
-- Use right-slot refolds (if switching to JP's template)
have r_refold := compat_refold_r_ak M r θ h_ext a k
have th_refold := compat_refold_θ_ak M r θ h_ext a k

-- Use fold helpers inside funext
funext k
simp [fold_sub_right, fold_add_left]  -- instead of ring
```

### For Field_simp Steps:
```lean
-- Bundle all nonzeros
have ⟨hr, hf, hD⟩ := Exterior.nonzeros_of_exterior h_ext
field_simp [hr, hf, hD]  -- exact forms, one call
ring
```

**Infrastructure Status:** ✅ Ready to use

---

## Build Status

**Current:**
- Errors: 0 ✅
- Sorries: 6 (detailed analysis above)
- Build Time: ~22 seconds
- All Section B infrastructure compiles cleanly

**Next Steps:** Await JP's guidance on implementation strategy

---

## Tactical Considerations

### Lesson from Section A/B

The successful pattern has been:
1. **Match what's there** (don't over-normalize)
2. **Fold, don't expand** (← add_mul, ← mul_add)
3. **Avoid global AC normalization** (local simpa only)
4. **One field_simp per lemma** (with exact hyps)
5. **Pure rewrite where possible** (refine, funext, rw)

### For Regroup Lemmas

Given their length (600+ lines) and nested structure, they may need:
- **Calc chains** for long derivations (like E3 integration)
- **Targeted lemmas** for each intermediate step (no long simp searches)
- **Fold helpers** inside binders (avoid ring in funext)

### For Ricci Identity

The existing BAK8 approach looks clean:
- Uses specialized distributors (no AC stalls)
- Relies on regroup lemmas for final assembly
- Should close quickly once regroup lemmas complete

---

## Commit History

1. **00b533e** - Complete Section A (6/6 tactical errors)
2. **46b9629** - Add Section B infrastructure (shims + refolds)
3. **d9c5b8d** - Update sorry line numbers

**Next:** Implement Section C based on JP's guidance

---

## Recommendation

**Proposed Approach:**

1. **Clarify with JP** which implementation path for regroup lemmas:
   - Existing (left-slot) vs. Template (right-slot)
   - Complete internal sorries vs. fresh implementation

2. **Start with highest leverage**:
   - If regroup lemmas can be completed quickly (filling 4 sorries), do that
   - Otherwise, work top-down: complete simple sorries that restore from bak8

3. **Test incrementally**:
   - Build after each sorry fix
   - Verify no regressions
   - Track line numbers as they shift

4. **Document progress**:
   - Update status report after each completion
   - Note any tactical insights
   - Track build times

---

## Questions for Next Session

1. Should I examine the bak files for completed proofs to guide implementation?
2. For `regroup_right_sum`: use right-slot refolds (JP's template) or continue left-slot approach?
3. Best entry point: bottom-up (regroup first) or top-down (simple sorries first)?
4. Timeline expectations: aim for all 6 complete, or prioritize critical path?

---

**Prepared by:** Claude Code (AI Agent)
**Date:** October 11, 2025
**Status:** Section B complete, Section C analyzed, awaiting implementation guidance

**Quote from JP:**
> "When you're ready to start Section B, drop in the two compat_refold_*_ak lemmas above
> and wire them into the same places you used the *_kb versions on the left."

**Status:** Section B complete ✅ Right-slot refolds added ✅ Ready for Section C wiring! 🚀
