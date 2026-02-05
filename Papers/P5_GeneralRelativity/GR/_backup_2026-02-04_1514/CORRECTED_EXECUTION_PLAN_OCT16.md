# Corrected Execution Plan: Phase 2B Fix and Continuation
## Date: October 16, 2025 (After JP/SP Review)

## Executive Summary

**Status**: Mathematical clarification received from JP/SP. Phase 2B had a **transcription error** in the lemma statement, not a mathematical issue. The Unified Strategy is sound.

**Action Items**:
1. ✅ Fix Phase 2B lemma statement (remove erroneous sum on RHS)
2. ✅ Complete Phase 2A differentiability infrastructure using provided helper lemmas
3. ⏳ Proceed to Phase 3 implementation

---

## 1. Phase 2B Correction (URGENT)

### 1.1 The Transcription Error

**INCORRECT (what was implemented)**:
```lean
lemma sum_k_prod_rule_to_Γ₁
    (M r θ : ℝ) (h_ext : Exterior M r θ) (a b : Idx) :
  sumIdx (fun k =>
    dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a * g M k b r θ) r θ
  - dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a * g M k b r θ) r θ)
  =
  sumIdx (fun k =>                                    -- ❌ WRONG: Sum on RHS
    dCoord Idx.r (fun r θ => Γ₁ M r θ k a Idx.θ) r θ  -- ❌ WRONG: k is first index
  - dCoord Idx.θ (fun r θ => Γ₁ M r θ k a Idx.r) r θ)
```

**Issue**: RHS incorrectly sums over k and uses wrong index position.

**CORRECT (per Unified Strategy)**:
```lean
lemma sum_k_prod_rule_to_Γ₁
    (M r θ : ℝ) (h_ext : Exterior M r θ) (a b : Idx) :
  sumIdx (fun k =>
    dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a * g M k b r θ) r θ
  - dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a * g M k b r θ) r θ)
  =
  dCoord Idx.r (fun r θ => Γ₁ M r θ b a Idx.θ) r θ    -- ✅ CORRECT: No sum
- dCoord Idx.θ (fun r θ => Γ₁ M r θ b a Idx.r) r θ    -- ✅ CORRECT: b is first index
```

**Mathematical justification** (from JP/SP memo):
```
Σ_k ∂_r(Γ^k_{θa} · g_{kb})
= ∂_r [ Σ_k (Γ^k_{θa} · g_{kb}) ]        [interchange ∂ and Σ]
= ∂_r [ Σ_k (Γ^k_{aθ} · g_{bk}) ]        [symmetries: Γ^k_{θa}=Γ^k_{aθ}, g_{kb}=g_{bk}]
= ∂_r [ Γ₁_{baθ} ]                        [definition: Γ₁_{baθ} = Σ_k g_{bk}·Γ^k_{aθ}]
```

**Key insight**: The sum over k is **consumed** by the definition of Γ₁. Index b propagates from g_{kb} to become the first index of Γ₁.

### 1.2 Implementation Steps for Phase 2B

**Step 1**: Fix the lemma statement (lines 6057-6066)
- Remove `sumIdx` wrapper from RHS
- Change `Γ₁ M r θ k a ...` to `Γ₁ M r θ b a ...`

**Step 2**: Implement proof using calc structure (estimated 80-120 lines):
1. Interchange ∂ and Σ (use Phase 2A lemmas)
2. Apply Γtot_symm (Γ^k_{θa} = Γ^k_{aθ})
3. Apply g_symm (g_{kb} = g_{bk})
4. Recognize Γ₁ definition
5. Done

**Estimated time**: 1-2 hours (straightforward application of symmetries)

---

## 2. Phase 2A Completion (Helper Lemmas)

### 2.1 Differentiability Infrastructure

JP/SP provided the mathlib pattern for product → curried conversion:

```lean
-- Add these helper lemmas (location: after line 401 in Riemann.lean)
lemma differentiableAt_slice_r {F : ℝ → ℝ → ℝ} {r θ : ℝ}
    (h_prod : DifferentiableAt ℝ (fun p : ℝ × ℝ => F p.1 p.2) (r, θ)) :
    DifferentiableAt ℝ (fun r' => F r' θ) r := by
  apply h_prod.comp r
  exact (differentiableAt_id'.prod (differentiableAt_const θ))

lemma differentiableAt_slice_θ {F : ℝ → ℝ → ℝ} {r θ : ℝ}
    (h_prod : DifferentiableAt ℝ (fun p : ℝ × ℝ => F p.1 p.2) (r, θ)) :
    DifferentiableAt ℝ (fun θ' => F r θ') θ := by
  apply h_prod.comp θ
  exact ((differentiableAt_const r).prod differentiableAt_id')
```

### 2.2 Update dCoord_r_sumIdx and dCoord_θ_sumIdx

Replace sorries (lines 6021, 6046) with:
```lean
-- In dCoord_r_sumIdx (line 6021):
exact differentiableAt_slice_r (h_diff k)

-- In dCoord_θ_sumIdx (line 6046):
exact differentiableAt_slice_θ (h_diff k)
```

**Estimated time**: 30 minutes

---

## 3. Phase 3: Riemann_via_Γ₁ (After Phase 2 Complete)

### 3.1 Overview

This is the **BOTTLENECK** - the core theorem connecting Riemann tensor to Γ₁.

**Location**: Lines 1319-1340 (currently skeleton with sorry)

**Estimated effort**: 250-400 lines, 8-16 hours

### 3.2 Structure (10-step calc proof)

Per Unified Strategy (lines 300-431):

**Steps 1-7**: Expansion and algebraic manipulation
- Step 1: Expand Riemann definition
- Step 2: Distribute g_kβ
- Step 3: Product rule backwards
- Step 4: Apply metric compatibility (∇g = 0)
- Step 5: Distribute nested sums
- Step 6: Apply Fubini (swap sum order)
- Step 7: Relabel dummy indices

**Step 8**: THE ALGEBRAIC MIRACLE ⚠️
- 12 ΓΓg terms → 4 terms
- **CRITICAL BOTTLENECK** (50-80 lines)
- May require 5-10 intermediate lemmas
- **STOP POINT**: Request JP/SP review at Step 8

**Steps 9-10**: Recognition and simplification
- Step 9: Recognize Γ₁ in ∂(Γ·g) terms
- Step 10: Final simplification

### 3.3 Implementation Strategy

**Phase 3A (Steps 1-7)**: Implementable now
- Straightforward expansions
- Use existing infrastructure
- **Estimated**: 100-150 lines, 3-5 hours

**Phase 3B (Step 8)**: STOP for review
- Document the 12 terms explicitly
- Show what needs to cancel
- Request JP/SP guidance on breakdown into lemmas
- **Do NOT attempt to complete this step alone**

**Phase 3C (Steps 9-10)**: After Step 8 review
- Should be straightforward once Step 8 is done
- **Estimated**: 50-80 lines, 2-3 hours

---

## 4. Execution Order

### Immediate (Next 2-3 hours)

1. **Fix Phase 2B lemma statement** (15 minutes)
   - Update lines 6057-6066
   - Verify type-checks

2. **Add differentiability helper lemmas** (15 minutes)
   - Add after line 401
   - Import Mathlib.Analysis.Calculus.FDeriv.Prod if needed

3. **Complete Phase 2A** (15 minutes)
   - Replace sorries with helper lemma calls
   - Build and verify

4. **Implement Phase 2B proof** (1-2 hours)
   - Calc structure with symmetries
   - Build and verify

5. **Build checkpoint** (5 minutes)
   - Verify 0 errors
   - Update status document

### Next Session (3-5 hours)

6. **Implement Phase 3 Steps 1-7** (3-5 hours)
   - Follow calc structure from Unified Strategy
   - Stop before Step 8

7. **Document Step 8 setup** (30 minutes)
   - List the 12 ΓΓg terms explicitly
   - Show target 4 terms
   - Create memo for JP/SP review

8. **STOP for mathematical review**

---

## 5. Success Criteria

### Phase 2 Complete
- ✅ Phase 2B lemma statement corrected
- ✅ Phase 2A helper lemmas added
- ✅ All Phase 2 proofs complete (no sorries)
- ✅ Build succeeds with 0 errors

### Phase 3 Steps 1-7 Complete
- ✅ Steps 1-7 implemented as calc proof
- ✅ All intermediate types correct
- ✅ Step 8 setup documented
- ⏸️ Stopped at Step 8 for review

### Not Required Yet
- ❌ Step 8 implementation (wait for review)
- ❌ Steps 9-10 (after Step 8)
- ❌ Phase 4 (after Phase 3 complete)

---

## 6. Risk Management

### Low Risk (Phases 2A/2B)
- Mathematical clarification received
- Implementation patterns clear
- Should complete without issues

### Medium Risk (Phase 3 Steps 1-7)
- Lots of detail work
- Many differentiability side conditions
- But structure is clear from Unified Strategy

### High Risk (Phase 3 Step 8)
- THE BOTTLENECK
- 12 terms → 4 terms cancellation
- **REQUIRES JP/SP GUIDANCE**
- DO NOT attempt without review

---

## 7. Documentation Updates

After each phase completion, update:

1. **IMPLEMENTATION_STATUS_OCT16.md**
   - Remove "with sorries" annotations as proofs complete
   - Update statistics

2. **PROGRESS_REPORT_PHASES_1_2.md**
   - Note correction of Phase 2B
   - Update to cover Phase 2 complete

3. Create new **PROGRESS_REPORT_PHASE_3_STEPS_1_7.md** when stopping at Step 8

---

## 8. Timeline Estimates

### Conservative (This Session)
- Phase 2B fix: 1.5 hours
- Phase 2A complete: 0.5 hours
- Build & verify: 0.5 hours
- **Total**: 2.5 hours

### Optimistic (Next Session)
- Phase 3 Steps 1-7: 3 hours
- Documentation: 0.5 hours
- **Total**: 3.5 hours

### Combined
- **Complete Phases 2A/2B + Phase 3 (Steps 1-7)**: 6 hours total
- **Stop point**: Ready for Step 8 review

---

## 9. Open Questions (For Later)

1. **Phase 4 integration**: Once Phase 3 complete, verify Phase 4 still works as planned
2. **Downstream impacts**: Check if Riemann_rθrθ_ext and other proofs need updates
3. **Differentiability discharge strategy**: Decide on axiom vs lemma approach for Phase 3

---

## 10. Approval Status

- ✅ **Mathematical approach**: Confirmed correct by JP/SP
- ✅ **Phase 2B fix**: Clear guidance provided
- ✅ **Phase 2A infrastructure**: Mathlib pattern provided
- ⏳ **Phase 3 Step 8**: Will need review when reached

---

**Prepared by**: Claude (AI Assistant)
**Date**: October 16, 2025
**Status**: Ready to execute Phase 2 fixes
**Next action**: Fix Phase 2B lemma statement per JP/SP guidance
