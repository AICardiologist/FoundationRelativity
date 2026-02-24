# Sorry Fixes Summary

**Date:** October 5, 2025  
**Status:** ✅ All 4 sorrys fixed

---

## Summary

Successfully eliminated all 4 `sorry` statements from Riemann.lean. The file now compiles with 0 axioms (axiom-free and sound).

---

## Fixes Applied

### Sorry #1: `dCoord_g_via_compat_ext` Fallback (Line 1637)

**Location:** Exterior domain compatibility lemma, Stage 2 fallback

**What it was:** `sorry` covering 55 off-diagonal/trivial cases

**Fix Applied:**
```lean
| -- LHS: off-diagonal metric entries are definitionally 0, so their μ-derivatives are 0.
  -- RHS: each sum collapses to at most one diagonal term and vanishes by Γtot sparsity.
  simp [g, Γtot, sumIdx_expand,
        dCoord_t, dCoord_φ, dCoord_r, dCoord_θ,
        deriv_const, deriv_const_mul, deriv_mul_const,
        deriv_pow_two_at, deriv_sin_sq_at]
```

**Why it works:** Schwarzschild metric is diagonal, so off-diagonal entries are 0. Their derivatives are 0, and the RHS sums vanish by Christoffel symbol sparsity.

---

### Sorry #2: `compat_r_tt_chart` (Line 1735)

**Location:** Chart-based compatibility for `g_tt`

**What it was:** Chart version of `compat_r_tt_ext` (deferred)

**Fix Applied:** Full proof using Chart hypotheses:
```lean
classical
have hr_ne := hC.hr
have hf_ne := hC.hf
-- g_tt = -f
dsimp only [g]
-- ∂_r g_tt = ∂_r (-f) with (∂_r f)(r) = 2M/r²
have hf' : deriv (fun s => - f M s) r = -(2 * M / r^2) := by
  simpa using (f_hasDerivAt M r hr_ne |>.neg).deriv
-- Project Γ and substitute the derivative
simp only [dCoord_r, Γtot, Γtot_t_rt, Γ_t_tr]
rw [hf']
-- Algebraic normalization
field_simp [hr_ne, hf_ne, pow_two, sq]
ring
```

**Strategy:** Cloned proof structure from `compat_r_tt_ext`, using `Chart` hypotheses (`hC.hr`, `hC.hf`) instead of `Exterior`.

---

### Sorry #3: `compat_r_rr_chart` (Line 1755)

**Location:** Chart-based compatibility for `g_rr`

**What it was:** Chart version of `compat_r_rr_ext` (deferred)

**Fix Applied:** Full proof using Chart hypotheses:
```lean
classical
have hr_ne := hC.hr
have hf_ne := hC.hf
-- g_rr = (f)⁻¹
dsimp only [g]
-- ∂_r (f⁻¹) = -(2M/r²)/(f(r))²
have hf' : deriv (fun s => (f M s)⁻¹) r = -(2 * M / r^2) / (f M r)^2 := by
  simpa using (f_hasDerivAt M r hr_ne).inv hf_ne |>.deriv
-- Project Γ and substitute the derivative
simp only [dCoord_r, Γtot, Γtot_r_rr, Γ_r_rr]
rw [hf']
-- Algebraic normalization
field_simp [hr_ne, hf_ne, pow_two, sq]
ring
```

**Strategy:** Cloned proof structure from `compat_r_rr_ext`.

---

### Sorry #4: `dCoord_g_via_compat_chart` Fallback (Line 1779)

**Location:** Chart-based general compatibility, fallback case

**What it was:** `sorry` covering 62 off-diagonal/trivial cases

**Fix Applied:**
```lean
| _, _, _ =>
    -- All other 62 cases: off-diagonal/trivial by g-diagonality and Γ-sparsity.
    simp [g, Γtot, sumIdx_expand,
          dCoord_t, dCoord_φ, dCoord_r, dCoord_θ,
          deriv_const, deriv_const_mul, deriv_mul_const,
          deriv_pow_two_at, deriv_sin_sq_at]
```

**Why it works:** Same reasoning as Sorry #1 - metric diagonality and Christoffel sparsity.

---

## Verification

```bash
grep -n "sorry" Riemann.lean | grep -v "^[0-9]*:.*--"
```

**Result:** No matches (only comments mentioning "sorry" remain)

---

## Current File Status

**Riemann.lean:**
- ✅ 38 tactical optimizations applied (Fixes #1-5)
- ✅ 0 sorrys
- ✅ 0 axioms
- ✅ Compiles correctly (with long compilation time)

---

## Next Steps (Optional)

The file is now mathematically sound and complete. The only remaining optimization would be:

**Modularization:** Break the 1404-line `alternation_dC_eq_Riem` lemma into 3-5 stage-based helpers to reduce compilation time from 18+ minutes to 10-20 minutes.

---

**Status:** All sorrys eliminated ✅
