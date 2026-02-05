# Component Lemma Tactical Issue - Request for Junior Professor

**Date:** October 5, 2025
**Context:** Implementing 6 Riemann component lemmas following your tactical guidance
**Status:** 4 component lemmas failing with `linarith` errors

---

## Summary

I successfully applied your tactical pattern to all 6 component lemmas:
- ✅ Added `hf_nz` hypotheses where needed
- ✅ Used `simpa [r_mul_f, mul_comm]` for `rmf` normalization
- ✅ Applied `field_simp` before final closure

However, the final closure tactic is failing. I changed from `ring` to `linarith [rmf]` to use the normalization hypothesis, but `linarith` cannot handle the nonlinear expressions after `field_simp`.

---

## Current Errors

**Build output:**
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:4986:2: linarith failed to find a contradiction
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:5016:2: linarith failed to find a contradiction
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:5038:2: linarith failed to find a contradiction
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:5060:2: linarith failed to find a contradiction
```

**Affected lemmas:**
- Line 4986: R_tφtφ
- Line 5016: R_rθrθ
- Line 5038: R_rφrφ
- Line 5060: R_θφθφ

Note: R_tθtθ (line 4964) works correctly, R_trtr (line 4941) uses `ring` successfully.

---

## Example: R_tφtφ (Lines 4967-4987)

**Current code:**
```lean
lemma Riemann_tφtφ_eq (M r θ : ℝ) (hM : 0 < M) (hr_ex : 2 * M < r) :
  Riemann M r θ Idx.t Idx.φ Idx.t Idx.φ = M * f M r * (Real.sin θ)^2 / r := by
  classical
  have hr_nz : r ≠ 0 := r_ne_zero_of_exterior M r hM hr_ex
  have hf_nz : f M r ≠ 0 := ne_of_gt (f_pos_of_hr M r hM hr_ex)

  -- Contract
  rw [Riemann_contract_first M r θ Idx.t Idx.φ Idx.t Idx.φ]
  simp [g]

  -- Expand RiemannUp - only λ=r term survives with Γ^r_{φφ}
  unfold RiemannUp
  simp [dCoord_t, dCoord_φ, sumIdx_expand, Γtot, Γ_t_tr, Γ_r_φφ]

  -- Use r_mul_f
  have rmf : r - 2*M = r * f M r := by
    simpa [r_mul_f M r hr_nz, mul_comm]

  field_simp [hr_nz, hf_nz, pow_two, sq]
  linarith [rmf]  -- ❌ FAILS HERE
```

**Goal at failure:**
I don't have the exact goal state, but after `field_simp`, the expression likely involves products and powers that `linarith` cannot handle.

---

## Question

**What tactic should close the goal after `field_simp`?**

I've tried:
- ❌ `ring` alone - doesn't use the `rmf` hypothesis to normalize `r - 2*M` terms
- ❌ `linarith [rmf]` - fails because goals are nonlinear after `field_simp`

**Possible approaches:**
1. Use `nlinarith [rmf]` for nonlinear arithmetic?
2. Rewrite with `rmf` before `field_simp`: `rw [rmf]` then `field_simp` then `ring`?
3. Use `simp [rmf]` instead of having it as a hypothesis?
4. Different tactical sequence altogether?

---

## Working Example: R_trtr (Lines 4909-4941)

This lemma **works correctly** with `ring`:

```lean
lemma Riemann_trtr_eq (M r θ : ℝ) (hM : 0 < M) (hr_ex : 2 * M < r) :
  Riemann M r θ Idx.t Idx.r Idx.t Idx.r = -(2*M) / r^3 := by
  classical
  have hr_nz : r ≠ 0 := r_ne_zero_of_exterior M r hM hr_ex
  have hf_nz : f M r ≠ 0 := ne_of_gt (f_pos_of_hr M r hM hr_ex)

  rw [Riemann_contract_first M r θ Idx.t Idx.r Idx.t Idx.r]
  unfold RiemannUp
  simp only [dCoord_t, dCoord_r, dCoord_θ, dCoord_φ, sumIdx_expand, Γtot]

  -- Apply derivative calculators
  have hder_tr : deriv (fun s => Γ_t_tr M s) r = -(2*M) * (r * f M r + M) / (r^4 * (f M r)^2) :=
    deriv_Γ_t_tr_at M r hr_nz hf_nz
  have hder_rr : deriv (fun s => Γ_r_rr M s) r = (2*M) * (r * f M r + M) / (r^4 * (f M r)^2) :=
    deriv_Γ_r_rr_at M r hr_nz hf_nz
  simp [hder_tr, hder_rr]

  -- Normalize
  have rmf : r - 2*M = r * f M r := by
    simpa [r_mul_f M r hr_nz, mul_comm]
  simp [Γ_t_tr, Γ_r_rr, Γ_r_tt, g, rmf, one_minus_f M r]

  field_simp [hr_nz, hf_nz, pow_two, sq]
  ring  -- ✅ WORKS
```

**Why does `ring` work here but not for R_tφtφ?**

---

## Comparison: R_tθtθ vs R_tφtφ

**R_tθtθ (WORKS with `linarith [rmf]` - line 4964):**
```lean
  have rmf : r - 2*M = r * f M r := by
    simpa [r_mul_f M r hr_nz, mul_comm]

  field_simp [hr_nz, hf_nz, rmf, pow_two, sq]
  linarith [rmf]  -- ✅ WORKS
```

**R_tφtφ (FAILS with `linarith [rmf]` - line 4986):**
```lean
  have rmf : r - 2*M = r * f M r := by
    simpa [r_mul_f M r hr_nz, mul_comm]

  field_simp [hr_nz, hf_nz, pow_two, sq]
  linarith [rmf]  -- ❌ FAILS
```

The only structural difference is R_tφtφ has `Real.sin θ` terms. Does this make it nonlinear?

---

## Files for Review

**Modified file:** `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean`

**Component lemmas:**
- Lines 4909-4941: R_trtr ✅ (uses `ring`, works)
- Lines 4944-4964: R_tθtθ ✅ (uses `linarith [rmf]`, works)
- Lines 4967-4987: R_tφtφ ❌ (uses `linarith [rmf]`, fails)
- Lines 4989-5016: R_rθrθ ❌ (uses `linarith [rmf]`, fails)
- Lines 5019-5038: R_rφrφ ❌ (uses `linarith [rmf]`, fails)
- Lines 5041-5060: R_θφθφ ❌ (uses `linarith [rmf]`, fails)

---

## Request

**Please advise on the correct closing tactic for these lemmas.**

Should I:
1. Use `nlinarith [rmf]` instead of `linarith [rmf]`?
2. Use `rw [rmf]` before `field_simp`, then close with `ring`?
3. Use a completely different approach?
4. Check if there's a goal state difference I'm missing?

I can provide the exact goal states at the failure points if that would help.

---

## Additional Context

**Pre-existing errors (not related to component lemmas):**
- Line 1939: Infrastructure differentiability
- Line 2188: Funext unification
- Line 2323: Simp no progress
- Lines 5094, 5144, 5183, 5215: Diagonal Ricci cases (likely depend on component lemmas)

**Total errors:** 11 (4 component lemma + 3 infrastructure + 4 diagonal Ricci)

---

## Your Original Guidance (for reference)

From earlier today, you recommended:
1. Contract first index using `Riemann_contract_first`
2. Expand `RiemannUp` only for concrete indices
3. Insert closed-form pieces (derivatives, Christoffel symbols)
4. Close with `field_simp` + `ring`

I followed this pattern but needed to use the `rmf` hypothesis to normalize `r - 2*M` terms, which led me to try `linarith [rmf]` instead of `ring`. This works for R_tθtθ but fails for the others.

---

**Generated:** October 5, 2025
**Priority:** HIGH - blocking Phase 2 completion
**Next step:** Apply your tactical correction to complete all 6 component lemmas
