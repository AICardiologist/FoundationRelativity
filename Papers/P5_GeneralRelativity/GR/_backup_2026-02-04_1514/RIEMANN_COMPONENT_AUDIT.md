# Riemann Component Audit for Ricci Proof

**Date:** 2025-10-02
**Purpose:** Identify which Riemann component lemmas exist for proving `Ricci_zero_ext`

---

## Ricci Components Needed

For `R_ab = Σ_ρ R_ρaρb`, we need 16 cases:

### Diagonal Components (4 cases)

**R_tt = R_tttt + R_rtrt + R_θtθt + R_φtφt**
- R_tttt: Should be 0 (first two indices equal) ✅ `Riemann_first_equal_zero_ext`
- R_rtrt: Need formula ✅ `Riemann_trtr_reduce` (line 4539)
- R_θtθt: Need formula ✅ `Riemann_tθtθ_reduce` (line 4557)
- R_φtφt: Need formula ✅ `Riemann_tφtφ_reduce` (line 4574)

**R_rr = R_trtर + R_rrrr + R_θrθr + R_φrφr**
- R_trtr: Same as R_rtrt (swap a,b) - use symmetry
- R_rrrr: Should be 0 ✅ `Riemann_first_equal_zero_ext`
- R_θrθr: Need formula - check for `Riemann_rθrθ_reduce` ✅ Found (line 4449)
- R_φrφr: Need formula - check for `Riemann_rφrφ_reduce` ✅ Found (line 4613)

**R_θθ = R_tθtθ + R_rθrθ + R_θθθθ + R_φθφθ**
- R_tθtθ: Same as R_θtθt - use symmetry
- R_rθrθ: Same as R_θrθr - use symmetry
- R_θθθθ: Should be 0 ✅ `Riemann_first_equal_zero_ext`
- R_φθφθ: Need formula - check for `Riemann_θφθφ_reduce` ✅ Found (line 4494)

**R_φφ = R_tφtφ + R_rφrφ + R_θφθφ + R_φφφφ**
- R_tφtφ: Same as R_φtφt - use symmetry
- R_rφrφ: Same as R_φrφr - use symmetry
- R_θφθφ: Same as R_φθφθ - use symmetry
- R_φφφφ: Should be 0 ✅ `Riemann_first_equal_zero_ext`

### Off-Diagonal Components (12 cases)

All should be zero because Schwarzschild is diagonal.

**R_tr = R_tttr + R_rtरr + R_θtθr + R_φtφr**
- R_tttr: Check zero lemma
- R_rtrr: Check zero lemma
- R_θtθr: Check zero lemma
- R_φtφr: Check zero lemma

**R_tθ = R_tttθ + R_rtrθ + R_θtθθ + R_φtφθ**
**R_tφ = R_tttφ + R_rtrφ + R_θtθφ + R_φtφφ**
**R_rθ = R_trθ + R_rrθ + R_θrθθ + R_φrφθ**
**R_rφ = R_trφ + R_rrφ + R_θrθφ + R_φrφφ**
**R_θφ = R_tθφ + R_rθφ + R_θθφφ + R_φθφφ**

(Plus 6 symmetric off-diagonal: R_rt, R_θt, R_φt, R_θr, R_φr, R_φθ)

---

## Audit Results

### Principal Component Formulas ✅

All 6 non-zero principal components have reduction lemmas:

1. ✅ `Riemann_trtr_reduce` (line 4539)
2. ✅ `Riemann_tθtθ_reduce` (line 4557)
3. ✅ `Riemann_tφtφ_reduce` (line 4574)
4. ✅ `Riemann_rθrθ_reduce` (line 4449)
5. ✅ `Riemann_rφrφ_reduce` (line 4613)
6. ✅ `Riemann_θφθφ_reduce` (line 4494)

### Symmetry Lemmas ✅

1. ✅ `Riemann_first_equal_zero_ext` - for R_aacd = 0
2. ✅ `Riemann_swap_a_b_ext` - for swapping first two indices
3. ✅ `Riemann_swap_c_d` - for swapping last two indices

### Zero Component Lemmas

Found ~60+ zero component lemmas (see grep results). Need to verify coverage for all terms in off-diagonal Ricci components.

---

## Next Steps

1. ✅ Audit complete - all principal formulas exist
2. ⏸️ Check if reduction formulas actually prove the components are zero (need to examine)
3. ⏸️ Implement Ricci_zero_ext using calculation pattern
4. ⏸️ Verify algebraically that diagonal components cancel to zero

---

## Key Insight

The reduction lemmas give FORMULAS, not zero proofs. We need to verify:
- Do these formulas algebraically cancel to give Ricci = 0?
- Or do we need additional lemmas proving the formulas equal zero?

This requires examining the actual RHS of the reduction lemmas.
