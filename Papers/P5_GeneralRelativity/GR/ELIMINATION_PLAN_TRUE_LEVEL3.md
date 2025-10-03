# Elimination Plan: TRUE LEVEL 3 (Zero Axioms, Zero Sorries)

**Date:** September 30, 2025
**Current Status:** 0 axioms ✅, 5 active sorries ⚠️
**Goal:** Eliminate all 5 sorries

---

## Overview

**5 active sorries to eliminate:**
1. Line 713: `dCoord_add` for arbitrary functions
2. Line 719: `dCoord_sub` for arbitrary functions
3. Line 725: `dCoord_mul` for arbitrary functions
4. Line 1953: `mu_t_component_eq` Stage-2 preview
5. Line 2010: `Riemann_alternation` main proof

---

## Strategy A: Delete Arbitrary Function Lemmas (Sorries 1-3)

**Estimated Time:** 3-4 hours

### Analysis

The 3 legacy lemmas (`dCoord_add/sub/mul`) are used in:

**Active uses:**
1. `dCoord_add4` (line 731) - used by `dCoord_add4_flat` → used by `dCoord_sumIdx_via_funext` → used by `dCoord_sumIdx`
2. `dCoord_sumIdx` (line 791) - uses `dCoord_add` directly
3. `RiemannUp_swap_mu_nu` (line 925) - simp mentions `dCoord_sub, dCoord_add`
4. `nabla_g_antisymmetry` (line 1463) - simp mentions `dCoord_sub`
5. Stage1 LHS lemmas (lines 1546, 1587, 1807, 1828, etc.)

**Key Insight:** When `simp [dCoord_add]` is called, simp doesn't necessarily use the named lemma - it uses **all `@[simp]` lemmas that match the pattern**. Since `dCoord_add_of_diff` is `@[simp]`, those simp calls may already be using the axiom-free version!

### Plan A: Option 1 - Delete and Test

**Steps:**
1. Comment out `dCoord_add/sub/mul` (lines 707-725)
2. Try to build
3. For each error, fix by:
   - Rewriting simp calls to not mention the deleted lemmas
   - Replacing explicit `rw` uses with direct application of `_of_diff` versions

**Expected errors:**
- `dCoord_add4`: Unknown identifier dCoord_add
- `dCoord_sumIdx`: Unknown identifier dCoord_add
- Possibly RiemannUp_swap_mu_nu and nabla_g_antisymmetry if simp really needs them

**Risk:** Medium - may discover unexpected uses

### Plan A: Option 2 - Replace with Axiom-Free Versions

**Steps:**
1. Replace `dCoord_add4` to use simp instead of rw:
```lean
lemma dCoord_add4 (μ : Idx) (A B C D : ℝ → ℝ → ℝ) (r θ : ℝ)
    (hA_r : DifferentiableAt_r A r θ ∨ μ ≠ Idx.r)
    (hB_r : DifferentiableAt_r B r θ ∨ μ ≠ Idx.r)
    (hC_r : DifferentiableAt_r C r θ ∨ μ ≠ Idx.r)
    (hD_r : DifferentiableAt_r D r θ ∨ μ ≠ Idx.r)
    (hA_θ : DifferentiableAt_θ A r θ ∨ μ ≠ Idx.θ)
    (hB_θ : DifferentiableAt_θ B r θ ∨ μ ≠ Idx.θ)
    (hC_θ : DifferentiableAt_θ C r θ ∨ μ ≠ Idx.θ)
    (hD_θ : DifferentiableAt_θ D r θ ∨ μ ≠ Idx.θ) :
  dCoord μ (fun r θ => A r θ + B r θ + C r θ + D r θ) r θ =
  dCoord μ A r θ + dCoord μ B r θ + dCoord μ C r θ + dCoord μ D r θ := by
  simp only [dCoord_add_of_diff]
  all_goals { assumption }
```

2. Update all call sites to provide differentiability proofs
3. Similarly for `dCoord_sumIdx`

**Risk:** High - requires propagating differentiability hypotheses through many lemmas

---

## Strategy B: Complete Stage-2 Preview (Sorry #4)

**Estimated Time:** 1-2 hours

### Current Code

```lean
lemma mu_t_component_eq :
    LHS_mu_t_chunk M r θ a b c d = RHS_mu_t_chunk M r θ a b c d := by
  /- Sketch (what we'd finish in Stage-2):
     * `simp` with your product-rule pushes (hpush_ct₁/_ct₂/_dt₁/_dt₂) to expand ∂(Γ⋅g)
     * apply metric compatibility `nabla_g_zero` to the ∂g terms
     * use `regroup_same_right` / `regroup₂` to pull common g-weights
     * unfold/align with the `RiemannUp` definition (μ=t row)
     The algebra is routine but verbose; we leave it as a placeholder for now. -/
  sorry
```

### Plan B: Follow the Sketch

**Steps:**
1. Read the helper lemmas `hpush_ct₁`, `hpush_ct₂`, `hpush_dt₁`, `hpush_dt₂` (should be defined nearby)
2. Apply simp with these product rules
3. Apply `nabla_g_zero` to ∂g terms (metric compatibility)
4. Use `regroup_same_right` and `regroup₂` (defined at lines 1964+)
5. Unfold and align with `RiemannUp` definition

**Risk:** Low - proof sketch is detailed and the algebra is "routine but verbose"

**Alternative:** Delete the entire `Stage2_mu_t_preview` namespace if it's not used

---

## Strategy C: Activate Alternation Proof (Sorry #5)

**Estimated Time:** 4-8 hours (depends on performance debugging)

### Current Status

Line 2010 has sorry with comment: "Early sorry due to Hsplit lemmas having performance issues"

Full proof scaffold exists in commented code (lines 2012-2614), but is marked "non-operational"

### Investigation Required

**Questions to answer:**
1. What are the "performance issues"? (timeout, memory, slow tactics?)
2. Is the proof scaffold mathematically correct?
3. Can we just uncomment and test?

### Plan C1: Try Uncommenting Proof Scaffold

**Steps:**
1. Uncomment lines 2012-2614 (the full proof scaffold)
2. Try to build with generous timeout (e.g., `set_option maxHeartbeats 1000000`)
3. If it times out, profile which tactics are slow
4. Optimize slow tactics

**Risk:** Medium-High - may discover fundamental issues

### Plan C2: Activate in Stages

Following the activation strategy in the comment:

**Step 1:** Uncomment `nabla_g_antisymmetry` proof
- Check if this builds
- Measure compile time

**Step 2:** Test build for regressions

**Step 3:** Uncomment Stage-1 LHS blocks (`Hsplit` lemmas in `Stage1_LHS_Splits`)
- These are at lines 1833, 1854
- These **already compile and work**!

**Step 4:** Test build - "each block is baseline-neutral"

**Step 5:** Uncomment unfold line and complete proof

**Risk:** Low-Medium - incremental approach with testing

---

## Strategy D: Simplify Approach - Focus on Critical Path

**Alternative Philosophy:** Accept some sorries in non-critical code

### Assessment

**Critical Path (Schwarzschild.lean):**
- ✅ 0 axioms, 0 sorries
- ✅ Publication-ready

**Non-Critical (Riemann.lean):**
- ✅ 0 axioms
- ⚠️ 5 sorries

**Question:** Are the 5 sorries in Riemann.lean blocking publication?

**Analysis:**
- Schwarzschild vacuum solution is the main result
- Riemann tensor alternation identity is foundational but may not be needed for vacuum proof
- Stage-2 preview is explicitly marked as preview/future work
- Arbitrary function lemmas are infrastructure

**Recommendation:** Consult professor on whether Schwarzschild.lean being sorry-free is sufficient

---

## Recommended Execution Order

### Phase 1: Low-Risk Wins (2-3 hours)

1. **Delete or complete Stage-2 preview** (sorry #4)
   - Either complete the proof following the sketch (1-2 hours)
   - Or delete the entire preview namespace (10 minutes)
   - **Recommendation:** Delete if not used, otherwise complete

2. **Test simp calls** for sorries #1-3
   - Check if `simp [dCoord_add]` actually needs the legacy lemma
   - May discover simp already uses `@[simp]` versions
   - Try commenting out legacy lemmas and building

### Phase 2: Medium-Risk Challenges (4-6 hours)

3. **Investigate alternation proof** (sorry #5)
   - Check what "performance issues" means
   - Try uncommenting proof scaffold with high timeout
   - Profile slow tactics
   - Attempt activation strategy

### Phase 3: High-Risk Refactoring (4-8 hours)

4. **Eliminate arbitrary function sorries** (#1-3)
   - Either delete lemmas and fix call sites
   - Or add differentiability hypotheses throughout
   - **Recommendation:** Defer until professor advises

---

## Timeline Estimates

**Optimistic (if everything works):** 4-6 hours
- Delete Stage-2 preview: 10 min
- Legacy lemmas already work via simp: 1 hour testing
- Alternation proof scaffold activates: 2-3 hours debugging

**Realistic (normal issues):** 10-15 hours
- Complete Stage-2 preview: 2 hours
- Refactor some legacy lemma uses: 3-4 hours
- Debug and activate alternation proof: 4-6 hours
- Fix unexpected issues: 2-3 hours

**Pessimistic (fundamental problems):** 20-30 hours
- Must rewrite alternation proof: 10-15 hours
- Must refactor all arbitrary function uses: 8-12 hours
- Debugging and iteration: 2-3 hours

---

## Decision Point

**Need professor input on:**
1. Which sorries are **blocking publication** vs. nice-to-have?
2. Is Schwarzschild.lean being sorry-free **sufficient**?
3. What are the "performance issues" with alternation proof?
4. Should we pursue TRUE LEVEL 3 or accept "Level 2.999"?

**If professor says:** "Schwarzschild.lean zero-sorry is sufficient for axiom calibration"
→ **DONE NOW** (0 additional hours)

**If professor says:** "Need TRUE LEVEL 3"
→ **10-30 hours** of work ahead (see timeline estimates)

---

**Current Status:** Awaiting professor guidance

🎯 **Next Step:** Review professor consultation memo and wait for guidance
