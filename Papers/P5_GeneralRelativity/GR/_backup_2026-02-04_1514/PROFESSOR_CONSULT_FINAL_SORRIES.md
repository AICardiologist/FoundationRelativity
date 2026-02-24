# Professor Consultation: Eliminating Final 5 Sorries for TRUE LEVEL 3

**Date:** September 30, 2025
**Context:** Axiom calibration - zero axioms achieved, need to eliminate 5 remaining sorries
**Goal:** TRUE LEVEL 3 (zero axioms, zero sorries)

---

## Current Achievement

✅ **Zero project axioms** - AX_differentiable_hack successfully eliminated
✅ **All automatic reasoning axiom-free** - simp uses `@[simp]` versions
✅ **Schwarzschild.lean (critical path): 0 axioms, 0 sorries**
⚠️ **Riemann.lean: 0 axioms, 5 active sorries**

---

## The 5 Active Sorries

### Category 1: Legacy Lemmas for Arbitrary Functions (3 sorries)

**Location:** Lines 713, 719, 725

**Code:**
```lean
lemma dCoord_add (μ : Idx) (f g : ℝ → ℝ → ℝ) (r θ : ℝ) :
  dCoord μ (fun r θ => f r θ + g r θ) r θ =
  dCoord μ f r θ + dCoord μ g r θ := by
  apply dCoord_add_of_diff
  all_goals { left; sorry }  -- Line 713

lemma dCoord_sub (μ : Idx) (f g : ℝ → ℝ → ℝ) (r θ : ℝ) :
  dCoord μ (fun r θ => f r θ - g r θ) r θ =
  dCoord μ f r θ - dCoord μ g r θ := by
  apply dCoord_sub_of_diff
  all_goals { left; sorry }  -- Line 719

lemma dCoord_mul (μ : Idx) (f g : ℝ → ℝ → ℝ) (r θ : ℝ) :
  dCoord μ (fun r θ => f r θ * g r θ) r θ =
  dCoord μ f r θ * g r θ + f r θ * dCoord μ g r θ := by
  apply dCoord_mul_of_diff
  all_goals { left; sorry }  -- Line 725
```

**Problem:** These lemmas work with **arbitrary functions** f and g. The sorry provides `DifferentiableAt f` for arbitrary f, which is unprovable without assumptions.

**Uses:**
- `dCoord_add4` (line 731): `rw [dCoord_add, dCoord_add, dCoord_add]`
- `dCoord_sumIdx` (line 791): `rw [dCoord_add, dCoord_add, dCoord_add]`
- `RiemannUp_swap_mu_nu` (line 925): `simp [... dCoord_sub, dCoord_add ...]`
- `nabla_g_antisymmetry` (line 1463): `simp only [... dCoord_sub]`
- Stage1 LHS lemmas (lines 1546, 1587, 1807, 1828, etc.)

**Question for Professor:**
How do we eliminate these sorries? Options:
1. **Add differentiability hypotheses** to all call sites? (would require refactoring ~15 uses)
2. **Delete these lemmas** and replace all uses with axiom-free `_of_diff` versions + explicit proofs?
3. **Keep them** and accept 3 sorries for arbitrary function infrastructure?
4. **Something else?**

---

### Category 2: Stage-2 Preview Lemma (1 sorry)

**Location:** Line 1953

**Code:**
```lean
namespace Stage2_mu_t_preview

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

**Problem:** This is a Stage-2 preview lemma showing the μ=t component computation. The proof sketch is provided but not completed.

**Uses:** None currently - this is preview/demonstration code

**Question for Professor:**
Should we:
1. **Complete the proof** following the sketch? (estimated 1-2 hours)
2. **Delete the preview lemma** entirely? (it's not used)
3. **Move to commented code** block to exclude from sorry count?
4. **Something else?**

---

### Category 3: Main Alternation Proof (1 sorry)

**Location:** Line 2010

**Code:**
```lean
lemma Riemann_alternation (M r θ : ℝ) (a b c d : Idx) :
    Riemann M r θ a b c d + Riemann M r θ a b d c = 0 := by
  /- ACTIVATION STRATEGY:
  [ ] Step 1: Uncomment nabla_g_antisymmetry proof (in previous section)
  [ ] Step 2: Test build - should have zero regressions (lemma is self-contained)
  [ ] Step 3: Uncomment Stage-1 LHS blocks (Hsplit lemmas in namespace Stage1_LHS_Splits)
  [ ] Step 4: Test build - each block is baseline-neutral
  [ ] Step 5: Uncomment unfold line (664) and complete proof
  -/

  -- NOTE: Early sorry due to Hsplit lemmas having performance issues
  -- The full proof scaffold is below but currently non-operational
  sorry

  /-
  -- Stage-1 splits (both families)
  have hC := Stage1_LHS_Splits.Hsplit_c_both M r θ a b c d
  have hD := Stage1_LHS_Splits.Hsplit_d_both M r θ a b c d

  [... full proof scaffold in comment ...]
  -/
```

**Problem:** Main alternation identity proof. The full proof scaffold exists in commented code below the sorry (lines 2012-2614), but is "non-operational" due to "performance issues" with Hsplit lemmas.

**Context:** This proves the first Bianchi identity: R_{abcd} + R_{abdc} = 0

**Uses:** The alternation identity is used in:
- Line 1932: `Riemann_swap_c_d` antisymmetry lemma
- This is foundational for the Riemann tensor structure

**Question for Professor:**
This is the most critical sorry. What's the path forward?
1. **Debug the "performance issues"** and activate the proof scaffold?
2. **Rewrite the proof** with a different approach?
3. **What are the "performance issues"** exactly? (timeout? memory? slow tactics?)
4. **Is the proof scaffold mathematically correct** but just slow?
5. **Can we optimize** the Hsplit lemmas to make them faster?

**Additional context:** The proof scaffold references:
- `Stage1_LHS_Splits.Hsplit_c_both` and `Hsplit_d_both` (lines 1833, 1854)
- These lemmas currently compile and work
- The full scaffold is 600+ lines of detailed algebra

---

## Summary of Sorries

| # | Location | Category | Critical? | Estimated Effort |
|---|----------|----------|-----------|------------------|
| 1-3 | 713, 719, 725 | Arbitrary function lemmas | Medium | 2-4 hours (refactor uses) |
| 4 | 1953 | Stage-2 preview | Low | 1-2 hours (complete proof) OR delete |
| 5 | 2010 | Main alternation proof | **HIGH** | Unknown (depends on perf issues) |

**Critical Path:** Sorry #5 (alternation proof) is the most important for mathematical completeness.

---

## Questions for Professor

### Primary Question
**What is the recommended approach to eliminate the 5 sorries for TRUE LEVEL 3?**

### Specific Questions

**Q1: Arbitrary function lemmas (sorries 1-3)**
- Is it acceptable to keep 3 sorries for arbitrary function linearity?
- Or should we refactor all ~15 call sites to use `_of_diff` versions?
- Is there a tactical pattern to avoid the sorries for abstract functions?

**Q2: Alternation proof (sorry #5)**
- What are the "performance issues" blocking the proof scaffold activation?
- Is the proof scaffold mathematically correct?
- Can we optimize the Hsplit lemmas?
- Should we try a completely different proof approach?
- **Is this sorry blocking publication**, or is the alternation identity not needed for the vacuum solution?

**Q3: Stage-2 preview (sorry #4)**
- Keep, complete, or delete?
- Is this preview valuable for future work?

**Q4: Publication Timeline**
- **How many of these 5 sorries MUST be eliminated** for publication?
- Is "zero axioms in critical path" (Schwarzschild.lean) sufficient?
- Or do we need TRUE LEVEL 3 (zero sorries everywhere)?

---

## Current Files Status

### Schwarzschild.lean
- ✅ 0 axioms
- ✅ 0 sorries
- ✅ Publication-ready

### Riemann.lean
- ✅ 0 axioms
- ⚠️ 5 active sorries
- ⚠️ Blocked by performance issues on alternation proof

---

## Recommendation Request

Please advise on:
1. **Priority order** for eliminating the 5 sorries
2. **Which sorries are blocking** publication vs. nice-to-have
3. **Specific tactical advice** for the alternation proof performance issue
4. **Timeline estimate** for TRUE LEVEL 3 (zero sorries)

---

## Build Status

✅ **All builds passing** (3078 jobs)

```bash
lake build Papers.P5_GeneralRelativity.GR.Schwarzschild  # ✅ 3077 jobs
lake build Papers.P5_GeneralRelativity.GR.Riemann        # ✅ 3078 jobs
```

---

**Awaiting guidance on path to TRUE LEVEL 3.**

🎯 **Zero axioms achieved - final push to zero sorries!**
