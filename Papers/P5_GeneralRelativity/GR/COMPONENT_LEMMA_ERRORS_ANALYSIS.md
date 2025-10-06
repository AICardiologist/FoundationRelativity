# Component Lemma Implementation Errors - Analysis for Junior Professor

**Date:** October 5, 2025
**Context:** Implementing 6 Riemann component lemmas per your tactical guidance
**Status:** 14 errors in component lemmas (+ 3 pre-existing infrastructure errors = 17 total)

---

## Background

Following your tactical pattern from earlier today, I implemented all 6 Riemann component lemmas:
1. R_trtr = -2M/r³ (line 4910-4931)
2. R_tθtθ = M·f(r)/r (line 4934-4952)
3. R_tφtφ = M·f(r)·sin²θ/r (line 4955-4972)
4. R_rθrθ = -M/(r·f(r)) (line 4975-4998)
5. R_rφrφ = -M·sin²θ/(r·f(r)) (line 5001-5019)
6. R_θφθφ = 2Mr·sin²θ (line 5022-5037)

**Your recommended pattern:**
1. Contract first index using `Riemann_contract_first`
2. Expand `RiemannUp` only for concrete indices
3. Insert closed-form pieces (derivatives, Christoffel symbols)
4. Close with `field_simp` + `ring`

---

## Error Summary

**New errors from component lemmas:** 8 errors
**Pre-existing infrastructure errors:** 3 errors (lines 1939, 2188, 2323)
**Diagonal Ricci case errors:** 4 errors (lines 5071, 5121, 5160, 5192)

---

## Detailed Error Analysis

### Error 1: Line 4927 - R_trtr derivative rewrite fails

**Error message:**
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:4927:6: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  deriv (fun s => Γ_t_tr M s) r
in the target expression
  -(f M r * ...)
```

**My code (lines 4926-4927):**
```lean
-- 3) Substitute closed derivative of Γ^t_{tr}
rw [deriv_Γ_t_tr M r hr_nz hf_nz hr2M]
```

**Issue:** After `simp [dCoord_t, dCoord_r, sumIdx_expand, Γtot, Γ_t_tr, Γ_r_rr]` on line 4924, the derivative term `deriv (fun s => Γ_t_tr M s) r` doesn't appear in the goal.

**Question:** Did the `simp` already expand/simplify away the derivative? How should I access the derivative term?

---

### Error 2-4: Lines 4935, 4956, 4976 - Unsolved goals after ring

**Error pattern (all three similar):**
```
error: unsolved goals
M r θ : ℝ
hM : 0 < M
hr_ex : 2 * M < r
```

**Affected lemmas:**
- Line 4935: R_tθtθ (after `ring` on line 4952)
- Line 4956: R_tφtφ (after `ring` on line 4972)
- Line 4976: R_rθrθ (after `ring` on line 4998)

**Pattern in all three:**
```lean
-- Contract first
rw [Riemann_contract_first M r θ Idx.? Idx.? Idx.? Idx.?]
simp [g]

-- Expand RiemannUp
unfold RiemannUp
simp [dCoord_?, dCoord_?, sumIdx_expand, Γtot, Γ_?, Γ_?]

-- Use helper lemma
have : r - 2*M = r * f M r := by simp [r_mul_f M r hr_nz]

-- Close algebra
field_simp [hr_nz, this, pow_two, sq]
ring  -- FAILS HERE
```

**Question:** Why doesn't `ring` close the goal? Is the expression not purely algebraic after `field_simp`? Do I need additional simplification before `ring`?

---

### Error 5: Line 5002 - R_rφrφ unsolved goals

Same pattern as errors 2-4.

---

### Error 6: Line 5023 - R_θφθφ unsolved goals

**Error:**
```
error: unsolved goals
M r θ : ℝ
hM : 0 < M
hr_ex : 2 * M < r
```

**My code (lines 5031-5037):**
```lean
-- Expand RiemannUp - pure Γ·Γ products (no derivatives)
unfold RiemannUp
simp [dCoord_θ, dCoord_φ, sumIdx_expand, Γtot, Γ_θ_φφ, Γ_φ_θφ, Γ_φ_φφ]

-- Use existing trig helper if available, otherwise direct algebra
field_simp [hr_nz, pow_two, sq]
ring  -- FAILS
```

---

### Error 7: Line 5033 - Unknown identifier Γ_φ_φφ

**Error:**
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:5033:65: Unknown identifier `Γ_φ_φφ`
```

**My code (line 5033):**
```lean
simp [dCoord_θ, dCoord_φ, sumIdx_expand, Γtot, Γ_θ_φφ, Γ_φ_θφ, Γ_φ_φφ]
                                                                  ^^^^^^^
```

**Issue:** `Γ_φ_φφ` doesn't exist (and shouldn't - it's zero by symmetry in Schwarzschild).

**Question:** What Christoffel symbols should I include in the simp list for R_θφθφ? I copied your example but `Γ_φ_φφ` was apparently wrong.

---

### Error 8: Line 4991 - R_rθrθ derivative issue

**My code (lines 4989-4998):**
```lean
-- ∂_r Γ^r_{θθ} where Γ^r_{θθ} = -(r - 2M)
-- The derivative is handled by simp expanding Γ_r_θθ = -(r - 2*M)
have : deriv (fun s => -(s - 2*M)) r = -1 := by
  simp [deriv_sub_const, deriv_id'']

-- Use r_mul_f
have rmf : r - 2*M = r * f M r := by simp [r_mul_f M r hr_nz]

field_simp [hr_nz, hf_nz, this, rmf, pow_two, sq]
ring
```

**Note:** This might be related to error 2-4 pattern.

---

## Pre-existing Infrastructure Errors (for reference)

These were already present before my changes:

**Error 9:** Line 1939 - `alternation_dC_eq_Riem` differentiability
**Error 10:** Line 2188 - funext unification
**Error 11:** Line 2323 - simp made no progress

---

## Questions for Junior Professor

### Q1: Derivative rewrite pattern (Error 1)
After `simp [... Γ_t_tr ...]`, the derivative term isn't in the goal. How should I:
- Either prevent simp from simplifying the derivative away?
- Or access the derivative in a different form?
- Or use a different lemma for the derivative?

### Q2: Ring failures (Errors 2-6)
Why doesn't `ring` close the goals after `field_simp`? The expressions should be pure algebra. Do I need:
- More lemmas in the `field_simp` list?
- A different normalization tactic before `ring`?
- To expand something else first?

### Q3: Missing/wrong Christoffel symbols (Error 7)
What's the correct simp list for R_θφθφ? I used `[Γ_θ_φφ, Γ_φ_θφ, Γ_φ_φφ]` but `Γ_φ_φφ` doesn't exist.

### Q4: General tactical sequence
Is my implementation of your pattern correct? The structure is:
```lean
rw [Riemann_contract_first ...]
simp [g]
unfold RiemannUp
simp [dCoord_*, sumIdx_expand, Γtot, Γ_* ...]
have : ... := by simp [helper_lemmas]
field_simp [...]
ring
```

Did I miss something or add something I shouldn't have?

---

## Files for Review

**Modified file:** `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean`
- Lines 4910-4931: R_trtr (Error 1)
- Lines 4934-4952: R_tθtθ (Error 2)
- Lines 4955-4972: R_tφtφ (Error 3)
- Lines 4975-4998: R_rθrθ (Error 4)
- Lines 5001-5019: R_rφrφ (Error 5)
- Lines 5022-5037: R_θφθφ (Errors 6-7)

**Build output:** `/tmp/final_build.txt` (full error details)

**Your original guidance:** Earlier in this session - tactical pattern for component lemmas

---

## Current Status

- ✅ Phase 1 (helper lemmas): Complete, 0 errors
- ❌ Phase 2 (component lemmas): 8 errors
- ❌ Pre-existing infrastructure: 3 errors
- ❌ Diagonal Ricci cases: 4 errors (likely depend on component lemmas)

**Total:** 17 compilation errors (was 7 before my changes)

---

**Generated:** October 5, 2025
**Priority:** HIGH - Need tactical corrections to complete component lemmas
**Next step:** Fix component lemma tactical issues, then diagonal Ricci cases should resolve
