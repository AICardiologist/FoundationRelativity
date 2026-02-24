# Surgical Fixes Application Report - Component Lemmas
**Date**: October 7, 2025
**Task**: Apply user's 8 surgical fixes (R1-R8) to resolve remaining tactical errors
**Result**: Partial success - Fixes applied as instructed, 7 errors remain due to pattern matching issues

---

## Executive Summary

✅ **Applied**: All 8 surgical fixes exactly as user specified
❌ **Status**: 7 compilation errors persist (pattern matching and goal state issues)
📊 **Progress**: Errors changed character - from "unsolved goals" to "pattern not found"

**Key Finding**: The expressions after `simp` do not contain the literal pattern `-(M * 2) + r` that the normalization lemmas expect. The goals have different syntactic forms like `2 * M - r` or `1 - 2 * M / r`.

---

## Build Command Used

```bash
cd /Users/quantmann/FoundationRelativity && lake build Papers.P5_GeneralRelativity.GR.Riemann
```

---

## Fixes Applied

### R1: RiemannUp_r_trt_ext (Lines 2032-2044)
**User's instruction**: Keep Γ_r_tt and Γ_t_tr symbolic for rewrite (Option A)

**Applied changes**:
```lean
-- Changed FROM:
simp [dCoord, sumIdx_expand, Γtot,
      Γtot_r_tt, Γtot_r_rr, Γtot_t_tr, Γtot_t_rt,
      Γ_r_tt, Γ_r_rr, Γ_t_tr]  -- expanded Γ symbols

-- TO:
simp [dCoord, sumIdx_expand, Γtot,
      Γtot_r_tt, Γtot_r_rr, Γtot_t_tr, Γtot_t_rt]  -- kept Γ_r_tt, Γ_t_tr symbolic

-- Then added normalization:
have hsub : r - 2*M ≠ 0 := by linarith [h_ext.hr_ex]
have hnorm : (-(M * 2) + r) = (r - 2*M) := by ring
rw [hnorm]
field_simp [hr, hsub, pow_two]
ring
```

**Result**: ❌ Error at line 2042
```
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  -(M * 2) + r
in the target expression
  deriv (fun s => M * (1 - 2 * M / s) / s ^ 2) r +
      (M * (1 - 2 * M / r) / r ^ 2 * (-M / (r ^ 2 * (1 - 2 * M / r))) +
        -M / (r ^ 2 * (1 - 2 * M / r)) * (M * (1 - 2 * M / r) / r ^ 2)) =
    -(2 * M * (1 - 2 * M / r)) / r ^ 3
```

**Analysis**:
- The goal has `1 - 2 * M / r` (which is `f M r`) instead of `-(M * 2) + r`
- The pattern `-(M * 2) + r` does not appear literally
- The `simp [f]` on line 2039 expanded `f` to `1 - 2*M/r`, creating a different form

---

### R2: RiemannUp_t_θtθ_ext (Lines 2079-2085)
**User's instruction**: Add `have hnorm : (-(M * 2) + r) = (r - 2*M) := by ring`, then `simp [hnorm]`

**Applied changes**:
```lean
have hsub : r - 2*M ≠ 0 := by linarith [h_ext.hr_ex]
have hnorm : (-(M * 2) + r) = (r - 2*M) := by ring
rw [hnorm]
simp only [f]
field_simp [hr, hsub]
ring_nf
```

**Result**: ❌ Error at line 2082
```
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  -(M * 2) + r
in the target expression
  M / (r ^ 2 * f M r) * (2 * M - r) = -M / r
```

**Analysis**:
- The goal has `2 * M - r` not `-(M * 2) + r`
- These are mathematically equal: `2*M - r = -(r - 2*M) = -(-( M*2) + r)` but different syntactically
- Need pattern: `2 * M - r` → `-(r - 2*M)`

---

### R3: RiemannUp_r_θrθ_ext (Lines 2099-2105)
**User's instruction**: Same pattern as R2

**Applied changes**: Identical to R2

**Result**: ❌ Error at line 2102 (same as R2 - pattern not found)

---

### R4: RiemannUp_φ_θφθ_ext (Lines 2115-2122)
**User's instruction**: Consolidate simp calls, drop trailing simp, use `try` block

**Applied changes**:
```lean
simp [dCoord, sumIdx_expand, Γtot,
      Γtot_θ_φφ, Γtot_φ_θφ, Γtot_φ_rφ, Γtot_r_φφ,
      Γ_θ_φφ, Γ_φ_θφ, Γ_φ_rφ, Γ_r_φφ, dφθφ]  -- consolidated with dφθφ
-- If any algebraic remainder with sin/cos:
try { field_simp [h_sin_nz, pow_two]; ring }
```

**Result**: ❌ Error at line 2110 (end of type signature)
```
error: unsolved goals
M r θ : ℝ
h_ext : Exterior M r θ
h_sin_nz : sin θ ≠ 0
hr : r ≠ 0
dφθφ : deriv (fun t => cos t * (sin t)⁻¹) θ = -1 / sin θ ^ 2
⊢ -deriv (fun t => cos t / sin t) θ + (r⁻¹ * Γ_r_θθ M r + -(cos θ / sin θ * (cos θ / sin θ))) = 2 * M / r
```

**Analysis**:
- The `simp` didn't fully expand/simplify
- Goal still has `Γ_r_θθ M r` unexpanded
- The derivative `deriv (fun t => cos t / sin t) θ` wasn't matched with `dφθφ` (which has `cos t * (sin t)⁻¹`)
- Division vs multiplication form mismatch: `cos t / sin t` ≠ `cos t * (sin t)⁻¹` syntactically

---

### R5: RiemannUp_t_φtφ_ext (Lines 2137-2142)
**User's instruction**: Add normalization with `hnorm`

**Applied changes**: Same pattern as R2

**Result**: ❌ Error at line 2139 (pattern not found - same as R2)

---

### R6: RiemannUp_r_φrφ_ext (Lines 2154-2159)
**User's instruction**: Add normalization with `hnorm`

**Applied changes**: Same pattern as R2

**Result**: ❌ Error at line 2156 (pattern not found - same as R2)

---

### R7-R8: RiemannUp_θ_φθφ_ext (Lines 2171-2178)
**User's instruction**: Consolidate simp, use `try` block to handle early goal closure

**Applied changes**:
```lean
-- Inside the proof of dθφφ (line 2173):
simp [deriv_neg, this]; ring

-- Main proof:
simp [dCoord, sumIdx_expand, Γtot,
      Γtot_θ_φφ, Γtot_θ_rθ, Γtot_r_φφ, Γtot_φ_θφ,
      Γ_θ_φφ, Γ_θ_rθ, Γ_r_φφ, Γ_φ_θφ, dθφφ]
-- If any algebraic remainder:
try { field_simp [hr, h_sin_nz, pow_two]; ring }
```

**Result**: ❌ Error at line 2173
```
error: No goals to be solved
warning: This simp argument is unused: deriv_neg
```

**Analysis**:
- The `ring` tactic on line 2173 (inside the `dθφφ` proof) closes the goal early
- But there's a `simp [deriv_neg, this]` before it that already closed the goal
- The `ring` is redundant and triggers "no goals"
- Need to remove `ring` from line 2173

---

## Detailed Diagnostics for Junior Professor

### Issue 1: Pattern Form Mismatch (Affects R1, R2, R3, R5, R6)

**Problem**: After `simp` expands expressions, the denominators don't have the form `-(M * 2) + r`

**Observed forms in goals**:
1. **R1**: `1 - 2 * M / r` (this is `f M r` expanded)
2. **R2, R3, R5, R6**: `2 * M - r` (negative of `r - 2*M`)

**Mathematical relationships**:
```
-(M * 2) + r  = r - 2*M   (target form for hnorm)
2*M - r       = -(r - 2*M)  (actual form in goal)
1 - 2*M/r     = (r - 2*M)/r (f expanded)
```

**Why `rw [hnorm]` fails**:
- `hnorm : -(M * 2) + r = r - 2*M`
- But goal has `2*M - r`, which is `-(r - 2*M)`, not `-(M * 2) + r`
- Lean's `rw` requires syntactic matching

**Possible solutions**:
1. **Add additional normalization lemmas**:
   ```lean
   have hnorm1 : 2*M - r = -(r - 2*M) := by ring
   have hnorm2 : r - 2*M = -(2*M - r) := by ring
   ```

2. **Use `ring_nf` to normalize before matching**:
   ```lean
   ring_nf  -- normalize both sides first
   have hsub : r - 2*M ≠ 0 := by linarith [h_ext.hr_ex]
   field_simp [hr, hsub]
   ring
   ```

3. **Don't expand `f` in simp, keep it symbolic longer**:
   ```lean
   simp [dCoord, sumIdx_expand, Γtot, ...]  -- without f
   -- Work with f symbolically
   have hsub : f M r ≠ 0 := Exterior.f_ne_zero h_ext
   field_simp [hr, hsub]
   simp only [f]  -- expand f only at the end
   ring
   ```

---

### Issue 2: Division vs Multiplication Forms (Affects R4)

**Problem**: Derivative expressions have mismatched forms

**In goal**: `deriv (fun t => cos t / sin t) θ`
**In lemma**: `dφθφ : deriv (fun t => cos t * (sin t)⁻¹) θ = ...`

**Why simp doesn't match**:
- Lean treats `/` and `* ⁻¹` as different syntactically
- Even though `div_eq_mul_inv` relates them, `simp` with `dφθφ` doesn't apply

**Possible solutions**:
1. **Add `div_eq_mul_inv` to simp list**:
   ```lean
   simp [dCoord, sumIdx_expand, Γtot, ..., dφθφ, div_eq_mul_inv]
   ```

2. **Rewrite division to multiplication first**:
   ```lean
   simp only [div_eq_mul_inv]  -- convert all / to * ⁻¹
   simp [dCoord, sumIdx_expand, Γtot, ..., dφθφ]
   ```

3. **State `dφθφ` in division form to match goal**:
   ```lean
   have dφθφ :
     deriv (fun t => cos t / sin t) θ = -1 / sin θ ^ 2 := by
     simp only [div_eq_mul_inv]
     simpa using deriv_Γ_φ_θφ_at θ h_sin_nz
   ```

---

### Issue 3: Early Goal Closure (Affects R7-R8)

**Problem**: Proof closes before all tactics are executed

**At line 2173** (inside `dθφφ` proof):
```lean
simp [deriv_neg, this]; ring
```

**Error**: `ring` triggers "No goals to be solved"

**Why**: The `simp [deriv_neg, this]` already closes the goal. The `ring` is unreachable.

**Solution**: Remove `ring` from line 2173:
```lean
simp [deriv_neg, this]  -- closes goal, no ring needed
```

---

## Complete Error Summary

| Error # | Lemma | Line | Type | Pattern Expected | Pattern in Goal |
|---------|-------|------|------|------------------|-----------------|
| 1 | RiemannUp_r_trt_ext | 2042 | Pattern not found | `-(M * 2) + r` | `1 - 2 * M / r` |
| 2 | RiemannUp_t_θtθ_ext | 2082 | Pattern not found | `-(M * 2) + r` | `2 * M - r` |
| 3 | RiemannUp_r_θrθ_ext | 2102 | Pattern not found | `-(M * 2) + r` | `2 * M - r` |
| 4 | RiemannUp_φ_θφθ_ext | 2110 | Unsolved goals | `cos t * (sin t)⁻¹` | `cos t / sin t` |
| 5 | RiemannUp_t_φtφ_ext | 2139 | Pattern not found | `-(M * 2) + r` | `2 * M - r` |
| 6 | RiemannUp_r_φrφ_ext | 2156 | Pattern not found | `-(M * 2) + r` | `2 * M - r` |
| 7 | RiemannUp_θ_φθφ_ext | 2173 | No goals | N/A | (goal already closed) |

---

## Recommended Fixes for Junior Professor

### Quick Fix for Errors 1-3, 5-6 (Normalization Issues)

Replace the `rw [hnorm]` approach with a more robust pattern:

```lean
-- Instead of:
have hsub : r - 2*M ≠ 0 := by linarith [h_ext.hr_ex]
have hnorm : (-(M * 2) + r) = (r - 2*M) := by ring
rw [hnorm]  -- FAILS: pattern not found

-- Use:
have hsub : r - 2*M ≠ 0 := by linarith [h_ext.hr_ex]
ring_nf  -- Normalize all arithmetic expressions first
field_simp [hr, hsub]  -- Now denominators match
ring
```

**Rationale**: `ring_nf` normalizes arithmetic to canonical forms, so `2*M - r` becomes `-(r - 2*M)`, which matches `hsub`.

---

### Quick Fix for Error 4 (Division Form)

Add `div_eq_mul_inv` to convert division before matching:

```lean
-- Before the main simp:
simp only [div_eq_mul_inv]  -- convert cos t / sin t → cos t * (sin t)⁻¹
simp [dCoord, sumIdx_expand, Γtot,
      Γtot_θ_φφ, Γtot_φ_θφ, Γtot_φ_rφ, Γtot_r_φφ,
      Γ_θ_φφ, Γ_φ_θφ, Γ_φ_rφ, Γ_r_φφ, dφθφ]
try { field_simp [h_sin_nz, pow_two]; ring }
```

---

### Quick Fix for Error 7 (Early Closure)

Remove redundant `ring` from line 2173:

```lean
-- Change FROM:
have : deriv (fun t => (Real.sin t) ^ 2) θ = 2 * Real.sin θ * Real.cos θ := by
  simpa [mul_comm] using Real.deriv_sin_sq θ
simp [deriv_neg, this]; ring  -- ring is redundant

-- TO:
have : deriv (fun t => (Real.sin t) ^ 2) θ = 2 * Real.sin θ * Real.cos θ := by
  simpa [mul_comm] using Real.deriv_sin_sq θ
simp [deriv_neg, this]  -- goal closes here
```

---

## Alternative Approach: Keep `f` Symbolic Longer

For errors 1-3, 5-6, instead of expanding `f` early and then trying to normalize, keep `f` symbolic:

```lean
-- Example for RiemannUp_t_θtθ_ext:
simp [dCoord, sumIdx_expand, Γtot,
      Γtot_t_tr, Γtot_r_θθ, Γtot_t_tθ, Γtot_t_θt,
      Γ_t_tr, Γ_r_θθ]
-- Now goal has f M r symbolically
have hsub : f M r ≠ 0 := Exterior.f_ne_zero h_ext
have hr_sub : r - 2*M ≠ 0 := by linarith [h_ext.hr_ex]
field_simp [hr, hsub]  -- clear f denominators
simp only [f]  -- expand f to (r - 2*M)/r
field_simp [hr, hr_sub]  -- now clear (r - 2*M) denominators
ring
```

**Rationale**: By keeping `f` symbolic until after the first `field_simp`, we avoid premature expansion into forms like `1 - 2*M/r` or `2*M - r`.

---

## Test Results Summary

**Build command**: `lake build Papers.P5_GeneralRelativity.GR.Riemann`

**Total errors**: 7 (down from 8 originally, down from 9 after user's first patches)

**Error categories**:
- 5 errors: "Pattern not found" (normalization issues)
- 1 error: "Unsolved goals" (division vs multiplication mismatch)
- 1 error: "No goals to be solved" (early closure)

**Warnings**: 14 unused simp arguments (non-blocking)

---

## Files Modified

**`GR/Riemann.lean`**
- Lines 2024-2044: RiemannUp_r_trt_ext (R1)
- Lines 2069-2085: RiemannUp_t_θtθ_ext (R2)
- Lines 2087-2105: RiemannUp_r_θrθ_ext (R3)
- Lines 2107-2122: RiemannUp_φ_θφθ_ext (R4)
- Lines 2127-2142: RiemannUp_t_φtφ_ext (R5)
- Lines 2144-2159: RiemannUp_r_φrφ_ext (R6)
- Lines 2161-2178: RiemannUp_θ_φθφ_ext (R7-R8)

---

## Conclusion

All 8 surgical fixes were applied exactly as the user specified. The remaining 7 errors are due to:

1. **Syntactic pattern mismatches**: The normalization lemma `hnorm : -(M * 2) + r = r - 2*M` doesn't match the actual forms in goals (`2*M - r`, `1 - 2*M/r`)

2. **Division vs multiplication forms**: Derivative expressions use `/` in goals but `* ⁻¹` in helper lemmas

3. **Early proof closure**: Extra tactics after goal is already solved

These are **tactical/syntactic issues**, not mathematical ones. The formulas are correct (verified by Senior Math Professor). The proofs need tactical adjustments to handle Lean's syntactic matching requirements.

**Recommended next step**: Apply the "Quick Fixes" above, which use `ring_nf`, `div_eq_mul_inv`, and keep `f` symbolic longer to avoid pattern matching failures.

---

**End of Report**
