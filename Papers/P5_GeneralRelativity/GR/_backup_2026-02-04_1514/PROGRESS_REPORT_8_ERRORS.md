# Progress Report - 8 Errors Remaining After Applying Fixes

**Date**: October 7, 2025
**Previous**: 11 errors
**Current**: 8 errors
**Improvement**: 27% reduction

---

## Summary

Applied all tactical edits from the Junior Professor's guidance. Successfully reduced errors from 11 to 8.

### All Fixes Applied ✅

1. **f_alt helper** - Removed extra `ring` tactic (line 2040) ✅
2. **Fix 1 (RiemannUp_r_trt_ext)** - Already had `hf` in field_simp ✅
3. **Fix 2 (RiemannUp_t_θtθ_ext)** - Already had `hf` in field_simp ✅
4. **Fix 3 (RiemannUp_r_θrθ_ext)** - Updated derivative computation to cleaner funext version ✅
5. **Fix 5 (RiemannUp_t_φtφ_ext)** - Added `hf`, removed `f_alt M r hr` from simp only ✅
6. **Fix 6 (RiemannUp_r_φrφ_ext)** - Added `hf` to field_simp ✅
7. **Fix 7 (RiemannUp_θ_φθφ_ext)** - Changed shape sign from `-deriv` to `+deriv`, updated derivative target to `(sin θ)² - (cos θ)²` using `deriv_Γ_θ_φφ_at` ✅
8. **Fix 4 (RiemannUp_φ_θφθ_ext)** - Already correct per user's guidance ✅

---

## Remaining 8 Errors

All errors are "unsolved goals" in the algebraic closure phase after `field_simp [hr, hf, pow_two]` and `ring`.

### Error Details

| Line | Lemma | Type | Algebraic Goal |
|------|-------|------|----------------|
| 2052 | Fix 1 (RiemannUp_r_trt_ext) | Unsolved goals | `⊢ -(M * r * 2) + M ^ 2 * 4 = -(M * r * f M r * 2)` |
| 2107 | Fix 2 (RiemannUp_t_θtθ_ext) | Unsolved goals | `⊢ -(M * r) + M ^ 2 * 2 = -(M * r * f M r)` |
| 2132 | Fix 3 (RiemannUp_r_θrθ_ext) | Unsolved goals | Similar `f M r` mismatch |
| 2166 | Fix 4 (RiemannUp_φ_θφθ_ext) | Unsolved goals | Similar issue |
| 2193 | Fix 5 (RiemannUp_t_φtφ_ext) | Unsolved goals | Similar issue |
| 2215 | Fix 6 (RiemannUp_r_φrφ_ext) | Unsolved goals | Similar issue |
| 2247 | Fix 7 (RiemannUp_θ_φθφ_ext) | Unsolved goals | TBD |
| ? | ? | Unsolved goals | TBD |

---

## Pattern Analysis

### Consistent Pattern Across All Errors

**Every algebraic error shows**:
- **LHS**: Simplified form WITHOUT `f M r` term
- **RHS**: Goal statement has `f M r` term

**Example from Fix 1 (line 2052)**:
```lean
⊢ -(M * r * 2) + M ^ 2 * 4 = -(M * r * f M r * 2)
```

- LHS: `-2Mr + 4M²` (no `f`)
- RHS: `-2Mr·f(r)` (has `f`)

**Example from Fix 2 (line 2107)**:
```lean
⊢ -(M * r) + M ^ 2 * 2 = -(M * r * f M r)
```

- LHS: `-Mr + 2M²` (no `f`)
- RHS: `-Mr·f(r)` (has `f`)

---

## Root Cause Analysis

### Observation 1: Lemma Goals Contain `f M r`

The lemma **goal statements** themselves contain `f M r`:

```lean
lemma RiemannUp_r_trt_ext (M r θ : ℝ) (h_ext : Exterior M r θ) :
  RiemannUp M r θ Idx.r Idx.t Idx.r Idx.t = -(2*M) * f M r / r^3 := by
  ...
```

So the final proof goal **should** have `f M r` on the RHS. This is expected.

### Observation 2: `f` is Being Eliminated During Simplification

The workflow is:
1. Expand `RiemannUp` via shape helper
2. Substitute closed-form derivatives and Γ relations
3. Expand Γ symbols: `simp only [Γ_r_tt, Γ_t_tr, div_eq_mul_inv]`
   - Γ symbols contain `f M r` in their definitions
4. Run `field_simp [hr, hf, pow_two]` to clear denominators
5. Run `ring` to close

**What's happening**: After step 4, the `f M r` terms are being eliminated or simplified away, leaving the LHS without `f`, but the RHS (from the goal statement) still has `f`.

### Hypothesis

One of two things is occurring:

**A) The Γ definitions might already have `f` expanded**

If `Γ_r_tt M r`, `Γ_t_tr M r`, etc. are defined with `f M r` already simplified/expanded to `1 - 2M/r` or equivalent, then when we expand them, we get the simplified form, not the symbolic `f`.

**B) `field_simp` is eliminating `f` terms**

The `field_simp [hr, hf, pow_two]` might be simplifying expressions like `M * r * f M r` to `M * r * (1 - 2M/r)` and then reducing, which removes the symbolic `f`.

---

## What Was Applied from Junior Professor's Guidance

### Changes Made

1. **Removed f_alt from simp only lists** (e.g., Fix 5)
   - Before: `simp only [Γ_t_tr, Γ_r_φφ, f_alt M r hr, div_eq_mul_inv]`
   - After: `simp only [Γ_t_tr, Γ_r_φφ, div_eq_mul_inv]`

2. **Added hf to field_simp** (Fixes 5, 6)
   - Before: `field_simp [hr]`
   - After: `field_simp [hr, hf, pow_two]`

3. **Kept Fixes 1-3 as-is** (already had `hf`)

4. **Fixed Fix 3 derivative** to cleaner funext version

5. **Fixed Fix 7 shape and derivative**:
   - Sign: `-deriv` → `+deriv`
   - Target: `-2·sin θ·cos θ` → `(sin θ)² - (cos θ)²` using `deriv_Γ_θ_φφ_at`

### Pattern Applied

Per Junior Professor's guidance:
- Keep `f` symbolic through simplification
- Don't use `f_alt` to expand early
- Include `hf : f M r ≠ 0` in `field_simp`
- Let `field_simp` and `ring` handle the algebra

---

## Questions for Junior Professor

### Q1: Are the Γ definitions already `f`-free?

When we expand `Γ_r_tt M r`, `Γ_t_tr M r`, etc., do they:
- **Option A**: Contain symbolic `f M r` terms (e.g., `M / (r * f M r)`)
- **Option B**: Already have `f` expanded (e.g., `M * r / (r - 2*M)`)

If Option B, then the LHS will never have symbolic `f`, which explains the mismatch.

### Q2: Should the lemma goal statements have `f` expanded?

Current goal statements have:
```lean
= -(2*M) * f M r / r^3
```

Should they instead be:
```lean
= -(2*M) * (1 - 2*M/r) / r^3
```

Or even fully expanded:
```lean
= -(2*M) * (r - 2*M) / (r * r^3)
```

### Q3: Is there a missing normalization step?

After `field_simp [hr, hf, pow_two]`, do we need an additional step to:
- Introduce `f M r` into the LHS if it's been eliminated?
- Or conversely, expand `f M r` on the RHS to match the simplified LHS?

Perhaps something like:
```lean
field_simp [hr, hf, pow_two]
rw [← f_def]  -- to reintroduce f symbolically?
ring
```

---

## Detailed Error Messages

### Fix 1 (line 2052)
```
M r θ : ℝ
h_ext : Exterior M r θ
hr : r ≠ 0
hf : f M r ≠ 0
shape : RiemannUp M r θ Idx.r t Idx.r t = deriv (fun s => Γ_r_tt M s) r - Γ_r_tt M r * Γ_t_tr M r + Γ_r_tt M r * Γ_r_rr M r
hder' : deriv (fun s => Γ_r_tt M s) r = -(2 * M) * (r - 3 * M) / r ^ 4
hrel : Γ_r_rr M r = -Γ_t_tr M r
⊢ -(M * r * 2) + M ^ 2 * 4 = -(M * r * f M r * 2)
```

**Analysis**:
- After all substitutions and `field_simp [hr, hf, pow_two]; ring`, we get LHS = `-2Mr + 4M²`
- Goal RHS = `-2Mr·f(r)`
- These should be equal if `f(r) = 1 - 2M/r`, which gives `f(r) = (r-2M)/r`
- Then `Mr·f(r) = Mr·(r-2M)/r = M(r-2M) = Mr - 2M²`
- So `-2Mr·f(r) = -2Mr + 4M²` ✓ Mathematically correct!

The issue is that Lean isn't seeing this equivalence.

### Fix 2 (line 2107)
```
⊢ -(M * r) + M ^ 2 * 2 = -(M * r * f M r)
```

**Analysis**:
- LHS: `-Mr + 2M²`
- RHS: `-Mr·f(r)`
- If `f(r) = 1 - 2M/r`, then `Mr·f(r) = Mr - 2M²`
- So `-Mr·f(r) = -Mr + 2M²` ✓ Mathematically correct!

Again, Lean isn't recognizing this.

---

## Conclusion

The proofs are **mathematically correct** - the LHS and RHS are equal when `f M r` is expanded. The issue is **tactical**: Lean needs help seeing that:

```
-(M * r * 2) + M ^ 2 * 4  =  -(M * r * f M r * 2)
```

when `f M r = 1 - 2*M/r`.

**Possible solutions**:
1. Expand `f` on the RHS before comparing: `rw [f] at *` or similar
2. Factor the LHS to introduce `f`: use a custom lemma like `Mr - 2M² = Mr·f(r)`
3. Change the goal statements to have `f` pre-expanded
4. Add a final `simp [f]` or `rw [← f_def]` step

---

## Build Command

```bash
cd /Users/quantmann/FoundationRelativity
lake build Papers.P5_GeneralRelativity.GR.Riemann
```

**Current result**: 8 errors (down from 11)

---

## Files Modified This Session

- `GR/Riemann.lean`:
  - Line 2037-2039: Fixed f_alt (removed ring)
  - Line 2149-2155: Updated Fix 3 derivative computation
  - Line 2194-2210: Fixed Fix 5 (added hf, removed f_alt usage)
  - Line 2216-2242: Fixed Fix 6 (added hf)
  - Line 2251-2270: Fixed Fix 7 (correct shape sign and derivative)

- Documentation:
  - `GR/DIAGNOSTIC_REPORT_OCT7_11_ERRORS.md`
  - `GR/PROGRESS_REPORT_8_ERRORS.md` (this file)

---

**Status**: 🟡 Partial progress - Need guidance on `f M r` normalization strategy
