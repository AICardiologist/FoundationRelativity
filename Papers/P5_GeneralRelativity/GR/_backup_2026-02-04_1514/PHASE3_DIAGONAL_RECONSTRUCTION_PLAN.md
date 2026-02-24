# Phase 3 Diagonal Cases Reconstruction Plan

**Date**: October 7, 2025
**Status**: CRITICAL REBUILD REQUIRED
**Cause**: Mathematical foundation was incorrect (Senior Math Prof verification)
**Scope**: Complete rewrite of 4 diagonal Ricci cases

---

## Executive Summary

**Problem**: The lemma `RiemannUp_first_equal_zero_ext` claims R^a_{cad} = 0, which is **mathematically FALSE**.

**Reality**: Individual terms R^a_{cad} are **non-zero**, but they **cancel when summed** to give R_cc = 0.

**Impact**: All 4 diagonal case proofs are invalid and must be completely rebuilt.

**Solution**: Prove explicit Riemann component values, then show algebraic cancellation.

**Estimated Effort**: 16-20 new lemmas + 4 rewritten proofs ≈ **Major refactoring**

---

## What Went Wrong

### The False Assumption

**Claimed** (line 1936):
```lean
@[simp] lemma RiemannUp_first_equal_zero_ext ... :
  RiemannUp M r θ a c a d = 0 := by
  sorry  -- Claims: R^a_{cad} = 0 (FALSE!)
```

**Comment said**: "This follows from antisymmetry in (a,c): R^a_{cad} = -R^c_{aad}"

**Math Prof verified**: This symmetry does NOT exist. The claim is FALSE.

### Counterexample (From Senior Math Prof)

**R^t_{rtr}** (a=t, c=r, d=r):

```
R^t_{rtr} = 2M/(r²(r-2M)) ≠ 0  ✗
```

**NOT zero!** The assumption was wrong.

### How the False Lemma Was Used

**Current diagonal case proofs** (lines 3381-3384):
```lean
case t.t => simp only [sumIdx_expand, RiemannUp_first_equal_zero_ext M r θ h_ext h_sin_nz]; norm_num
case r.r => simp only [sumIdx_expand, RiemannUp_first_equal_zero_ext M r θ h_ext h_sin_nz]; norm_num
case θ.θ => simp only [sumIdx_expand, RiemannUp_first_equal_zero_ext M r θ h_ext h_sin_nz]; norm_num
case φ.φ => simp only [sumIdx_expand, RiemannUp_first_equal_zero_ext M r θ h_ext h_sin_nz]; norm_num
```

**Logic**:
- Expand sum: R_cc = R^t_{ctc} + R^r_{crc} + R^θ_{cθc} + R^φ_{cφc}
- Apply false lemma: Each term = 0
- Conclude: 0 + 0 + 0 + 0 = 0 ✓

**Problem**: The lemma is false, so the proofs are invalid!

### The Correct Picture (From Senior Math Prof)

**Example: R_rr**

```
R_rr = R^t_{rtr} + R^r_{rrr} + R^θ_{rθr} + R^φ_{rφr}

WHERE:
  R^t_{rtr} = +2M/(r²(r-2M))   [NON-ZERO!]
  R^r_{rrr} = 0                 [True by standard antisymmetry R^a_{bcc}=0]
  R^θ_{rθr} = -M/(r²(r-2M))    [NON-ZERO!]
  R^φ_{rφr} = -M/(r²(r-2M))    [NON-ZERO!]

SUM = 2M/(r²(r-2M)) - M/(r²(r-2M)) - M/(r²(r-2M))
    = (2M - M - M)/(r²(r-2M))
    = 0 ✓  [CANCELLATION!]
```

**Key insight**: The terms are non-zero but **cancel algebraically**.

---

## Reconstruction Strategy

### Phase A: Remove Invalid Infrastructure

**Action**: Delete the false lemma and document why

**Affected Code**:
- Line 1936-1945: `RiemannUp_first_equal_zero_ext` (DELETE)
- Lines 3381-3384: Diagonal case proofs (REWRITE)

**Status**: Prepare for deletion (backup first)

### Phase B: Prove Component Lemmas

**Goal**: Prove explicit values for non-zero Riemann components

**Required for each diagonal case**: 2-4 component lemmas

**Total estimated**: ~16 component lemmas

### Phase C: Prove Cancellation

**Goal**: Rewrite diagonal cases to show explicit algebraic cancellation

**Method**: Substitute component values, simplify algebraically

---

## Detailed Work Plan

### Stage 1: Preparation and Backup ✅

#### Task 1.1: Create Backup
**Action**: Save current state before making changes
```bash
cp GR/Riemann.lean GR/Riemann.lean.before_diagonal_reconstruction
git stash push -m "Before diagonal reconstruction - false lemma state"
```

#### Task 1.2: Document Current State
**Action**: Create snapshot of what's being replaced
**Deliverable**: List of all code that will be deleted/changed

#### Task 1.3: Verify Off-Diagonal Cases
**Action**: Confirm 12 off-diagonal lemmas are still valid (don't use false property)
**Expected**: All 12 should be fine (they don't rely on RiemannUp_first_equal_zero_ext)

---

### Stage 2: Remove Invalid Code 🗑️

#### Task 2.1: Remove False Lemma
**File**: GR/Riemann.lean
**Line**: 1936-1945
**Action**: Delete `RiemannUp_first_equal_zero_ext` entirely

**Replacement**: Add comment explaining why it was removed
```lean
/-- REMOVED: RiemannUp_first_equal_zero_ext
    Previous version claimed R^a_{cad} = 0 (when first and third indices equal).
    This is mathematically FALSE (verified by Senior Math Prof, Oct 7, 2025).

    Counterexample: R^t_{rtr} = 2M/(r²(r-2M)) ≠ 0

    The correct statement is that these components are non-zero but CANCEL when summed.
    See component lemmas below for explicit values.
-/
```

#### Task 2.2: Comment Out Diagonal Cases
**File**: GR/Riemann.lean
**Lines**: 3381-3384
**Action**: Comment out with explanation

```lean
-- DIAGONAL CASES - UNDER RECONSTRUCTION
-- Previous proofs relied on false lemma RiemannUp_first_equal_zero_ext
-- Must be rebuilt using explicit component values and algebraic cancellation
-- See PHASE3_DIAGONAL_RECONSTRUCTION_PLAN.md

/-
case t.t => simp only [sumIdx_expand, RiemannUp_first_equal_zero_ext M r θ h_ext h_sin_nz]; norm_num
case r.r => simp only [sumIdx_expand, RiemannUp_first_equal_zero_ext M r θ h_ext h_sin_nz]; norm_num
case θ.θ => simp only [sumIdx_expand, RiemannUp_first_equal_zero_ext M r θ h_ext h_sin_nz]; norm_num
case φ.φ => simp only [sumIdx_expand, RiemannUp_first_equal_zero_ext M r θ h_ext h_sin_nz]; norm_num
-/

-- TODO: Rebuild using component lemmas (see Stage 3)
case t.t => sorry
case r.r => sorry
case θ.θ => sorry
case φ.φ => sorry
```

#### Task 2.3: Verify Build
**Action**: Run `lake build` to confirm no NEW errors from removal
**Expected**: Should compile with 4 sorries (the diagonal cases)

---

### Stage 3: Prove Component Lemmas (MAJOR WORK) 🔧

This is the bulk of the effort. For each diagonal case, we need explicit component values.

#### Case r.r: R_rr = 0

**Required Components** (from Senior Math Prof memo):

##### Lemma 3.1.1: R^t_{rtr}
```lean
lemma RiemannUp_t_rtr_ext (M r θ : ℝ) (h_ext : Exterior M r θ) (h_sin_nz : Real.sin θ ≠ 0) :
  RiemannUp M r θ Idx.t Idx.r Idx.t Idx.r = 2*M / (r^2 * (r - 2*M)) := by
  -- Strategy:
  -- 1. Unfold RiemannUp definition
  -- 2. Substitute Christoffel symbols (most are zero)
  -- 3. Compute derivatives
  -- 4. Algebraic simplification
  sorry  -- NEEDS: Junior Tactics Prof
```

**Proof outline**:
```lean
unfold RiemannUp
simp only [dCoord, Γtot]
-- Substitute known Christoffel values:
-- Γ^t_{rr} = 0
-- Γ^t_{tr} = M/(r(r-2M))
-- Γ^r_{rr} = -M/(r(r-2M))
-- Most others are zero by sparsity

-- After substitution, goal becomes:
-- ⊢ -∂_r(Γ^t_{tr}) + Γ^t_{tr} * Γ^r_{rr} - (Γ^t_{tr})^2 = 2M/(r²(r-2M))

-- Compute derivative:
have deriv_Γttr : deriv (fun r => M/(r*(r-2*M))) r = -M*(2*r-2*M)/(r*(r-2*M))^2 := by
  -- Calculus
  sorry

-- Substitute and simplify:
rw [deriv_Γttr]
field_simp [h_ext.r_pos, h_ext.r_ne_2M]
ring
```

**Difficulty**: MEDIUM-HIGH (calculus + algebra)
**Needs**: Junior Tactics Prof for derivative computation tactics

##### Lemma 3.1.2: R^r_{rrr}
```lean
lemma RiemannUp_r_rrr_ext (M r θ : ℝ) (h_ext : Exterior M r θ) (h_sin_nz : Real.sin θ ≠ 0) :
  RiemannUp M r θ Idx.r Idx.r Idx.r Idx.r = 0 := by
  -- This is TRUE by standard antisymmetry: R^a_{bcc} = 0
  -- Should be provable from RiemannUp_swap_mu_nu
  sorry
```

**Difficulty**: LOW (standard symmetry)
**May already have**: Check if follows from existing `RiemannUp_swap_mu_nu`

##### Lemma 3.1.3: R^θ_{rθr}
```lean
lemma RiemannUp_θ_rθr_ext (M r θ : ℝ) (h_ext : Exterior M r θ) (h_sin_nz : Real.sin θ ≠ 0) :
  RiemannUp M r θ Idx.θ Idx.r Idx.θ Idx.r = -M / (r^2 * (r - 2*M)) := by
  -- Similar to 3.1.1 but simpler (Senior Math Prof: equals (1/r)*Γ^r_{rr})
  unfold RiemannUp
  -- Key insight from memo: R^θ_{rθr} = (1/r)*Γ^r_{rr}
  sorry  -- NEEDS: Junior Tactics Prof
```

**Difficulty**: MEDIUM
**Hint**: Senior Math Prof said this equals (1/r)*Γ^r_{rr}, which might simplify proof

##### Lemma 3.1.4: R^φ_{rφr}
```lean
lemma RiemannUp_φ_rφr_ext (M r θ : ℝ) (h_ext : Exterior M r θ) (h_sin_nz : Real.sin θ ≠ 0) :
  RiemannUp M r θ Idx.φ Idx.r Idx.φ Idx.r = -M / (r^2 * (r - 2*M)) := by
  -- By spherical symmetry, identical to R^θ_{rθr}
  sorry  -- NEEDS: Junior Tactics Prof
```

**Difficulty**: MEDIUM (similar to 3.1.3)

##### Lemma 3.1.5: Cancellation Proof
```lean
lemma Ricci_rr_cancellation (M r θ : ℝ) (h_ext : Exterior M r θ) (h_sin_nz : Real.sin θ ≠ 0) :
  RiemannUp M r θ Idx.t Idx.r Idx.t Idx.r +
  RiemannUp M r θ Idx.r Idx.r Idx.r Idx.r +
  RiemannUp M r θ Idx.θ Idx.r Idx.θ Idx.r +
  RiemannUp M r θ Idx.φ Idx.r Idx.φ Idx.r = 0 := by
  -- Substitute component values
  rw [RiemannUp_t_rtr_ext M r θ h_ext h_sin_nz,
      RiemannUp_r_rrr_ext M r θ h_ext h_sin_nz,
      RiemannUp_θ_rθr_ext M r θ h_ext h_sin_nz,
      RiemannUp_φ_rφr_ext M r θ h_ext h_sin_nz]
  -- Goal: 2M/(r²(r-2M)) + 0 + (-M/(r²(r-2M))) + (-M/(r²(r-2M))) = 0
  field_simp [h_ext.r_pos, h_ext.r_ne_2M]
  ring
```

**Difficulty**: LOW (pure algebra, should be automatic)

#### Case t.t: R_tt = 0

**Required Components**:

##### Lemma 3.2.1: R^t_{ttt}
```lean
lemma RiemannUp_t_ttt_ext : RiemannUp M r θ Idx.t Idx.t Idx.t Idx.t = 0 := by
  -- Standard antisymmetry R^a_{bcc} = 0
  sorry
```

##### Lemma 3.2.2: R^r_{trt}
```lean
lemma RiemannUp_r_trt_ext : RiemannUp M r θ Idx.r Idx.t Idx.r Idx.t = ??? := by
  -- Need to calculate
  sorry
```

##### Lemma 3.2.3: R^θ_{tθt}
```lean
lemma RiemannUp_θ_tθt_ext : RiemannUp M r θ Idx.θ Idx.t Idx.θ Idx.t = ??? := by
  sorry
```

##### Lemma 3.2.4: R^φ_{tφt}
```lean
lemma RiemannUp_φ_tφt_ext : RiemannUp M r θ Idx.φ Idx.t Idx.φ Idx.t = ??? := by
  sorry
```

##### Lemma 3.2.5: Cancellation
```lean
lemma Ricci_tt_cancellation : ... = 0 := by
  rw [component lemmas]
  field_simp; ring
```

#### Case θ.θ: R_θθ = 0

**Required Components**: ~4 lemmas (similar pattern)

#### Case φ.φ: R_φφ = 0

**Required Components**: ~4 lemmas (similar pattern)

**Note**: By spherical symmetry, many φ components might be identical to θ components.

---

### Stage 4: Rewrite Diagonal Cases 📝

#### Task 4.1: Case r.r
```lean
case r.r =>
  unfold RicciContraction
  simp only [sumIdx_expand]
  exact Ricci_rr_cancellation M r θ h_ext h_sin_nz
```

**Difficulty**: TRIVIAL (once cancellation lemma proven)

#### Task 4.2: Case t.t
```lean
case t.t =>
  unfold RicciContraction
  simp only [sumIdx_expand]
  exact Ricci_tt_cancellation M r θ h_ext h_sin_nz
```

#### Task 4.3: Case θ.θ
```lean
case θ.θ =>
  unfold RicciContraction
  simp only [sumIdx_expand]
  exact Ricci_θθ_cancellation M r θ h_ext h_sin_nz
```

#### Task 4.4: Case φ.φ
```lean
case φ.φ =>
  unfold RicciContraction
  simp only [sumIdx_expand]
  exact Ricci_φφ_cancellation M r θ h_ext h_sin_nz
```

---

### Stage 5: Verification and Testing ✅

#### Task 5.1: Build Verification
```bash
lake build Papers.P5_GeneralRelativity.GR.Riemann
```
**Expected**: 0 errors, 0 sorries

#### Task 5.2: Verify Main Theorem
**Check**: `Ricci_zero_ext` still compiles and proves Ricci = 0

#### Task 5.3: Documentation Update
**Update**:
- INFRASTRUCTURE_CLEANUP_COMPLETION_REPORT.md (no longer 0 sorries!)
- Create PHASE3_DIAGONAL_RECONSTRUCTION_COMPLETION.md

---

## Component Lemma Summary

### Total Required Lemmas (Estimate)

| Case | Non-trivial Components | Trivial (antisymmetry) | Cancellation | Total |
|------|------------------------|------------------------|--------------|-------|
| r.r  | 3 (R^t_{rtr}, R^θ_{rθr}, R^φ_{rφr}) | 1 (R^r_{rrr}=0) | 1 | 5 |
| t.t  | 3 (R^r_{trt}, R^θ_{tθt}, R^φ_{tφt}) | 1 (R^t_{ttt}=0) | 1 | 5 |
| θ.θ  | 3 | 1 | 1 | 5 |
| φ.φ  | 3 | 1 | 1 | 5 |
| **Total** | **12** | **4** | **4** | **20** |

**Breakdown**:
- **12 non-trivial component lemmas**: Require RiemannUp expansion, Christoffel substitution, derivative computation, algebraic simplification
- **4 trivial components**: Use standard R^a_{bcc} = 0 antisymmetry
- **4 cancellation lemmas**: Pure algebra (should be automatic)

### Difficulty Assessment

**Non-trivial component lemmas**:
- **Difficulty**: MEDIUM-HIGH
- **Bottleneck**: Derivative computation and algebraic manipulation
- **Needs**: Junior Tactics Prof for tactical guidance

**Cancellation lemmas**:
- **Difficulty**: LOW
- **Should be automatic**: `field_simp` + `ring`

**Total Effort Estimate**:
- If we have good tactics: 1-2 days (with Junior Prof help)
- If we struggle with tactics: 1-2 weeks

---

## Risk Assessment

### Risk 1: Component Lemma Proofs Get Stuck
**Probability**: MEDIUM-HIGH
**Impact**: HIGH (blocks entire reconstruction)
**Mitigation**:
- Start with ONE component (R^t_{rtr}) as proof-of-concept
- If stuck, immediately consult Junior Tactics Prof
- May need to develop derivative computation infrastructure

### Risk 2: Algebraic Cancellation Fails
**Probability**: LOW
**Impact**: MEDIUM (suggests algebraic error)
**Mitigation**:
- Verify algebra by hand first
- Check component values match Senior Math Prof's examples
- Use `polyrith` or `nlinarith` if `ring` fails

### Risk 3: Missing Christoffel Symbol Lemmas
**Probability**: MEDIUM
**Impact**: MEDIUM (need to prove auxiliary facts)
**Mitigation**:
- Audit existing Christoffel symbol infrastructure
- Identify gaps early
- Prove needed facts as helper lemmas

### Risk 4: Spherical Symmetry Not Formalized
**Probability**: LOW-MEDIUM
**Impact**: MEDIUM (θ and φ cases might not be identical)
**Mitigation**:
- May need to prove θ and φ cases separately
- Check if spherical symmetry is already in codebase

---

## Dependencies and Blockers

### Required Infrastructure (Should Already Exist)

✅ **Christoffel symbols**: All Γ^a_{bc} values defined and proven
✅ **RiemannUp definition**: Lines 1639-1643
✅ **Derivative machinery**: `dCoord`, `deriv` functions
✅ **Algebraic tactics**: `field_simp`, `ring`

### Potentially Missing

❓ **Derivative lemmas**: e.g., `deriv (fun r => M/(r(r-2M))) r = ...`
❓ **Product/quotient rules**: For computing Christoffel derivatives
❓ **Spherical symmetry formalization**: R^θ_{...} = R^φ_{...} for matching indices

### Will Definitely Need

🎯 **Junior Tactics Professor**: For derivative computation and algebraic manipulation tactics
🎯 **Testing framework**: Verify each component lemma independently before integration

---

## Timeline (Optimistic)

### Week 1: Proof of Concept
- **Day 1-2**: Remove false lemma, verify build with sorries
- **Day 3-4**: Prove ONE component lemma (R^t_{rtr}) to validate approach
- **Day 5**: Prove cancellation for case r.r to validate full chain

### Week 2: Scale Up
- **Day 1-3**: Prove remaining components for case t.t
- **Day 4-5**: Prove components for cases θ.θ and φ.φ (may go faster with established patterns)

### Week 3: Integration and Testing
- **Day 1-2**: Integrate all component lemmas
- **Day 3**: Rewrite all 4 diagonal case proofs
- **Day 4**: Full build verification
- **Day 5**: Documentation and cleanup

**Total**: 3 weeks (optimistic, with Junior Prof assistance)

### Timeline (Realistic)

Add 50-100% buffer for:
- Getting stuck on difficult component proofs
- Finding missing infrastructure
- Debugging tactical issues
- Consulting Senior/Junior Profs

**Total**: 4-6 weeks

---

## Success Criteria

### Stage Completion Criteria

**Stage 1**: ✅ Backup created, current state documented
**Stage 2**: ✅ False lemma removed, build works with 4 sorries
**Stage 3**: ✅ All 20 component lemmas proven (0 sorries in lemmas)
**Stage 4**: ✅ All 4 diagonal cases rewritten and proven (0 sorries in cases)
**Stage 5**: ✅ Full build: 0 errors, 0 sorries, main theorem proven

### Final Verification

**Must verify**:
1. `lake build Papers.P5_GeneralRelativity.GR.Riemann` → 0 errors
2. `grep -c "sorry" GR/Riemann.lean` → 0
3. Main theorem `Ricci_zero_ext` proven without sorries
4. All component values match Senior Math Prof's examples

---

## Consultation Strategy

### When to Consult Junior Tactics Prof

**Immediate**:
- Starting proof of R^t_{rtr} (proof-of-concept)
- If derivative computation tactics are unclear
- If algebraic simplification gets stuck

**As Needed**:
- Each time a component proof gets stuck
- If pattern emerges across multiple cases (can generalize tactics)

### When to Re-Consult Senior Math Prof

**If**:
- Component values don't match memo examples
- Cancellation doesn't work algebraically
- Unexpected zero or non-zero components found
- Spherical symmetry assumptions unclear

---

## Rollback Plan

**If reconstruction fails catastrophically**:

### Option 1: Partial Rollback
- Keep off-diagonal cases (they're fine)
- Mark diagonal cases as admitted/axiomatized
- Document as "future work"

### Option 2: Full Rollback
- Revert to commit before reconstruction
- Document the false lemma issue
- Keep as "known issue" until resources available

### Option 3: Alternative Approach
- Consult Senior Math Prof for different proof strategy
- May exist coordinate-free or symmetry-based approach we haven't considered

---

## Next Immediate Actions

### Action 1: Create Backup ⏰
```bash
cd /Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity
cp GR/Riemann.lean GR/Riemann.lean.before_diagonal_reconstruction
git add GR/Riemann.lean
git commit -m "Snapshot before diagonal reconstruction (has false lemma)"
```

### Action 2: Remove False Lemma ⏰
- Delete RiemannUp_first_equal_zero_ext
- Add explanatory comment
- Comment out diagonal cases with explanation

### Action 3: Verify Clean State ⏰
```bash
lake build Papers.P5_GeneralRelativity.GR.Riemann
# Should: compile with 4 sorries (diagonal cases)
```

### Action 4: Prepare Consultation Request ⏰
- Draft questions for Junior Tactics Prof
- Focus on R^t_{rtr} proof-of-concept
- Include specific tactical questions about derivative computation

---

## Open Questions

1. **Do we have derivative lemmas for Christoffel symbols?**
   - Need: `deriv (Γ^t_{tr}) = ...`
   - May need to prove these as auxiliary lemmas

2. **Is spherical symmetry formalized?**
   - Can we prove R^θ_{aθb} = R^φ_{aφb} systematically?
   - Or must prove each separately?

3. **What's the best tactic for derivative + algebraic combo?**
   - Junior Tactics Prof should advise
   - May need custom tactic development

4. **Can we extract patterns to reduce duplication?**
   - Many component lemmas have similar structure
   - Could we metaprogram or use lemma templates?

---

## Appendix: Senior Math Prof's Examples

### Example 1: R_rr = 0

```
R_rr = R^t_{rtr} + R^r_{rrr} + R^θ_{rθr} + R^φ_{rφr}

R^t_{rtr} = +2M/(r²(r-2M))
R^r_{rrr} = 0  (antisymmetry)
R^θ_{rθr} = -M/(r²(r-2M))
R^φ_{rφr} = -M/(r²(r-2M))

Sum = 2M/(r²(r-2M)) - M/(r²(r-2M)) - M/(r²(r-2M)) = 0 ✓
```

**Insight**: R^θ_{rθr} = (1/r) * Γ^r_{rr}

### Example 2: R^t_{rtr} Derivation

```
R^t_{rtr} = ∂_t Γ^t_{rr} - ∂_r Γ^t_{tr} + Σ_e Γ^t_{te} Γ^e_{rr} - Σ_e Γ^t_{re} Γ^e_{tr}

Using:
- Γ^t_{rr} = 0
- Γ^t_{tr} = M/(r(r-2M))
- Γ^r_{rr} = -M/(r(r-2M))
- Most others zero

Simplifies to:
R^t_{rtr} = 0 - ∂_r Γ^t_{tr} + Γ^t_{tr} Γ^r_{rr} - (Γ^t_{tr})²

= -∂_r(M/(r(r-2M))) + M/(r(r-2M)) * (-M/(r(r-2M))) - (M/(r(r-2M)))²

= -∂_r(Γ^t_{tr}) - 2(Γ^t_{tr})²

Computing derivative:
∂_r(M/(r²-2Mr)) = -M(2r-2M)/(r²-2Mr)²

Final:
R^t_{rtr} = M(2r-2M)/(r²-2Mr)² - 2M²/(r²-2Mr)²
          = (2Mr - 2M² - 2M²)/(r²(r-2M)²)
          = 2M(r-2M)/(r²(r-2M)²)
          = 2M/(r²(r-2M))
```

---

**Plan Status**: COMPLETE
**Ready to Execute**: Yes (pending user approval)
**Next Step**: Action 1 (Create Backup)

---

**Prepared by**: Claude Code
**Date**: October 7, 2025
**Reviewed by**: [Awaiting user approval]
