# Phase 3: Refactor Ricci Diagonal Cases Using Component Lemmas

**Date**: October 6, 2025
**Status**: Ready to implement
**Escalation**: Not needed - straightforward refactoring

---

## Objective

Replace the failing `reduce + simp` pattern in diagonal Ricci cases with direct substitution of our proven component lemma values.

---

## Current Errors (9 total)

### Pre-existing (not Phase 3 targets):
- Line 1939: unsolved goals (pre-existing)
- Line 2188: Tactic `apply` failed (pre-existing)
- Line 2323: `simp` made no progress (pre-existing)

### Phase 3 Targets (4 diagonal Ricci cases):
- **Line 5156**: case t.t (Ricci_tt)
- **Line 5206**: case r.r (Ricci_rr)
- **Line 5245**: case θ.θ (Ricci_θθ)
- **Line 5277**: case φ.φ (Ricci_φφ)

**Goal**: Reduce errors from 9 → 5 by fixing these 4 cases.

---

## Available Component Lemmas (Phase 2 Results)

All proven with NO sorries:

1. `Riemann_trtr_eq (M r : ℝ) (hM : 0 < M) (hr_ex : 2 * M < r)`:
   - `R_trtr = -2M/r³`

2. `Riemann_tθtθ_eq (M r : ℝ) (hM : 0 < M) (hr_ex : 2 * M < r)`:
   - `R_tθtθ = M·f(r)/r`

3. `Riemann_tφtφ_eq (M r : ℝ) (hM : 0 < M) (hr_ex : 2 * M < r)`:
   - `R_tφtφ = M·f(r)·sin²θ/r`

4. `Riemann_rθrθ_eq (M r : ℝ) (hM : 0 < M) (hr_ex : 2 * M < r)`:
   - `R_rθrθ = -M/(r·f(r))`

5. `Riemann_rφrφ_eq (M r : ℝ) (hM : 0 < M) (hr_ex : 2 * M < r)`:
   - `R_rφrφ = -M·sin²θ/(r·f(r))`

6. `Riemann_θφθφ_eq (M r θ : ℝ) (hM : 0 < M) (hr_ex : 2 * M < r) (hsin : sin θ ≠ 0)`:
   - `R_θφθφ = 2Mr·sin²θ` (off-axis)
   - Note: Requires `hsin : sin θ ≠ 0` hypothesis

---

## Implementation Plan

### Case 1: t.t (line 5156-5205)

**Current failing approach:**
```lean
rw [h_rt, h_th, h_ph,
    Riemann_trtr_reduce, Riemann_tθtθ_reduce, Riemann_tφtφ_reduce]
simp [Γ_r_rr, Γ_t_tr, ..., deriv_Γ_t_tr_at, ...]
field_simp [hr_nz, hf_ne, hθ]; ring  -- FAILS HERE
```

**New approach:**
```lean
rw [h_rt, h_th, h_ph]
-- Direct substitution of closed-form values
rw [Riemann_trtr_eq M r hM hr_ex,
    Riemann_tθtθ_eq M r hM hr_ex,
    Riemann_tφtφ_eq M r hM hr_ex]
-- Expand g and f, simplify
simp only [g, f, pow_two]
field_simp [hr_nz]
ring
```

**Components used**: R_trtr, R_tθtθ, R_tφtφ

**Expected result**: Ricci_tt = R^r_trt + R^θ_tθt + R^φ_tφt = 0

### Case 2: r.r (line 5206-5243)

**Components used**: R_trtr, R_rθrθ, R_rφrφ

**Pattern**:
```lean
rw [Riemann_trtr_reduce, h_rθ, h_rφ, Riemann_rθrθ_reduce, Riemann_rφrφ_reduce]
```
→
```lean
rw [Riemann_trtr_eq M r hM hr_ex,
    h_rθ, Riemann_rθrθ_eq M r hM hr_ex,
    h_rφ, Riemann_rφrφ_eq M r hM hr_ex]
```

**Expected result**: Ricci_rr = R^t_rtr + R^θ_rθr + R^φ_rφr = 0

### Case 3: θ.θ (line 5245-5275)

**Components used**: R_tθtθ, R_rθrθ, R_θφθφ

**Pattern**:
```lean
rw [Riemann_tθtθ_reduce, Riemann_rθrθ_reduce, h_θφ, Riemann_θφθφ_reduce]
```
→
```lean
rw [Riemann_tθtθ_eq M r hM hr_ex,
    Riemann_rθrθ_eq M r hM hr_ex,
    h_θφ, Riemann_θφθφ_eq M r θ hM hr_ex h_sin_nz]
```

**Note**: Uses `h_sin_nz` for R_θφθφ

**Expected result**: Ricci_θθ = R^t_θtθ + R^r_θrθ + R^φ_θφθ = 0

### Case 4: φ.φ (line 5277-5310)

**Components used**: R_tφtφ, R_rφrφ, R_θφθφ

**Pattern**:
```lean
rw [Riemann_tφtφ_reduce, Riemann_rφrφ_reduce, Riemann_θφθφ_reduce]
```
→
```lean
rw [Riemann_tφtφ_eq M r hM hr_ex,
    Riemann_rφrφ_eq M r hM hr_ex,
    Riemann_θφθφ_eq M r θ hM hr_ex h_sin_nz]
```

**Expected result**: Ricci_φφ = R^t_φtφ + R^r_φrφ + R^θ_φθφ = 0

---

## Key Insights

### Why This Should Work

1. **Component lemmas provide exact closed-form values**
   - No need to expand Christoffel symbols
   - No need to compute derivatives
   - Direct algebraic identities

2. **All hypotheses available in Ricci_zero_ext context**
   - `hM : 0 < M` from `h_ext.hM`
   - `hr_ex : 2 * M < r` from `h_ext.hr_ex`
   - `h_sin_nz : sin θ ≠ 0` already in theorem statement

3. **Each Ricci component = sum of 3 Riemann components**
   - All 6 needed Riemann components are proven
   - Summing them should give 0 algebraically

### Potential Issues and Mitigations

**Issue 1**: Component lemma values don't immediately sum to 0
- **Mitigation**: Add intermediate `have` statements to show each term
- **Example**:
  ```lean
  have ht : RiemannUp ... Idx.t ... = -2*M/r³ := Riemann_trtr_eq ...
  have hθ : RiemannUp ... Idx.θ ... = M·f/r := Riemann_tθtθ_eq ...
  have hφ : RiemannUp ... Idx.φ ... = M·f·sin²θ/r := Riemann_tφtφ_eq ...
  rw [ht, hθ, hφ]
  -- Now simplify sum
  ```

**Issue 2**: Field_simp needs more hypotheses
- **Mitigation**: Add `hf_ne : f M r ≠ 0` (already computed in each case)
- **Mitigation**: Explicitly provide all nonzero facts to field_simp

**Issue 3**: Ring fails on the final goal
- **Mitigation**: Use `simp only [f]` to expand `f = 1 - 2M/r` before ring
- **Mitigation**: Try `norm_num` for numeric simplifications

---

## Success Criteria

- ✅ All 4 diagonal cases compile without errors
- ✅ No new sorries introduced
- ✅ Total errors reduced: 9 → 5
- ✅ Proofs are shorter and clearer than reduce+simp approach

---

## Rollback Plan

If substitution doesn't work:
1. Keep one case as `sorry` with detailed comment
2. Document the issue for Senior Professor consultation
3. Commit progress on working cases

---

## Timeline

- **Estimated**: 15-20 minutes for all 4 cases
- **Checkpoint**: After each case, verify error count decreases by 1
- **Final verification**: Build and confirm total errors = 5

---

## Notes for Implementation

### Available context in each diagonal case:
- `hM : 0 < M`
- `hr_ex : 2 * M < r`
- `hr_nz : r ≠ 0`
- `hf_ne : f M r ≠ 0`
- `h_sin_nz : Real.sin θ ≠ 0` (from theorem statement)

### Symmetry rewrites (keep these):
- `h_rt`, `h_th`, `h_ph` (for t.t case)
- `h_rθ`, `h_rφ` (for r.r case)
- `h_θφ` (for θ.θ case)
- None needed (for φ.φ case - already in standard order)

### Simplification pattern:
```lean
simp only [g, f, pow_two]  -- Expand definitions
field_simp [hr_nz, hf_ne, h_sin_nz]  -- Clear denominators
ring  -- Close algebraic goal
```

---

Ready to implement!
