# Iteration Report - Component Lemma Fixes

## Summary

Attempted to implement the uniform post-shape pipeline for all 7 Schwarzschild Riemann component lemmas. **Significant progress made**, but **16 tactical errors remain** that require precise edits.

---

## ✅ Successfully Implemented

### 1. Normalization Helper Lemmas (lines 2036-2044)
```lean
lemma f_alt (M r : ℝ) : f M r = (r - 2*M) / r := by unfold f; ring
lemma twoM_sub_r (M r : ℝ) : 2*M - r = -(r - 2*M) := by ring
lemma inv_sub_flip (M r : ℝ) : (-(M*2) + r) = (r - 2*M) := by ring
```

### 2. Uniform 2-Phase field_simp Pattern
Applied to all 7 lemmas:
```lean
rw [shape]
simp_rw [hder']  -- if derivative
simp only [Γ_..., div_eq_mul_inv]

-- Phase A: clear denominators without expanding f
have hf : f M r ≠ 0 := Exterior.f_ne_zero h_ext
field_simp [hr, hf, pow_two]

-- Phase B: expand f and normalize
have hsub : r - 2*M ≠ 0 := by linarith [h_ext.hr_ex]
simp only [f_alt, div_eq_mul_inv, twoM_sub_r]
field_simp [hr, hsub, pow_two]
ring
```

### 3. Removed Invalid Inner Shields
Section-level shields (lines 2023-2032) are sufficient.

### 4. Used `rw` and `simp_rw` Instead of Bare `simp`
For precise control over rewrites.

---

## 🚧 Remaining Issues (16 Errors)

### Error Categories

#### Category A: Unused Γtot Terms in Shapes
**Errors**: Lines 2075, 2200, 2213, 2232, 2297, 2310

**Pattern**: Linter warns "`Γtot_*` is unused" → shape helper has extra terms

**Example (Fix 2, line 2125)**:
```lean
simp only [RiemannUp, dCoord_t, dCoord_θ,
           sumIdx_expand, Γtot, Γtot_t_tr, Γtot_r_θθ, Γtot_t_θt]
                                   ^^^^^^^^^ unused!
```

**Status**: Partially fixed (removed `Γtot_t_tr` from Fixes 1 and 2), but more remain.

---

#### Category B: Shape Helper Algebraic Closure
**Errors**: Lines 2123, 2153, 2198, 2258, 2295

**Pattern**: Shape has derivative or product terms that `ring` can't normalize

**Example (Fix 2, line 2123)**:
```
⊢ -deriv (fun t => 0) θ + Γ_t_tr M r * Γ_r_θθ M r = Γ_t_tr M r * Γ_r_θθ M r
```
The `-deriv (fun t => 0) θ` term should simplify to 0 but doesn't.

**Example (Fix 6, line 2258)**:
```
⊢ deriv (fun s => Γ_r_φφ M s θ) r + (Γ_r_rr M r * Γ_r_φφ M r θ - Γ_r_φφ M r θ * Γ_φ_rφ r)
  = Γ_r_rr M r * Γ_r_φφ M r θ
```
The `deriv` term should cancel with something in the shape, but it's not.

---

#### Category C: "No Goals to be Solved"
**Errors**: Lines 2139, 2246

**Pattern**: Too many tactics applied after goal already closed

**Example (Fix 2, line 2139)**:
After `ring_nf` closes the goal, there's likely an extra `ring` or other tactic.

---

#### Category D: Other Type/Progress Issues
**Errors**: Lines 2164 (type mismatch - partially fixed), 2144, 2251

---

## 📊 Detailed Error List

| Line | Lemma  | Error Type | Description |
|------|--------|------------|-------------|
| 2038 | f_alt  | unfold fail | Fixed: changed to `unfold f; ring` |
| 2075 | Fix 1  | simp no progress | After shape, simp on Γ's makes no progress |
| 2123 | Fix 2  | unsolved goals | Derivative term in shape not cleaned |
| 2139 | Fix 2  | no goals | Extra tactic after closure |
| 2153 | Fix 3  | unsolved goals | Derivative + product terms in shape |
| 2164 | Fix 3  | type mismatch | Fixed: corrected derivative form |
| 2144 | Fix 3  | unsolved goals | After shape substitution |
| 2198 | Fix 4  | unsolved goals | After derivative substitution |
| 2213 | Fix 4  | simp no progress | After shape |
| 2246 | Fix 5  | no goals | Extra tactic |
| 2258 | Fix 6  | unsolved goals | Derivative in shape |
| 2251 | Fix 6  | unsolved goals | After shape |
| 2295 | Fix 7  | unsolved goals | After derivative substitution |
| 2310 | Fix 7  | simp no progress | After shape |

---

## 🎯 Root Cause Analysis

The uniform pipeline is **structurally correct**, but individual lemmas need **lemma-specific tactical adjustments**:

1. **Shapes aren't always the minimal form** → Extra derivative or zero terms survive `ring`
2. **Some Γtot terms in simp only lists are unused** → Linter warnings + potential interference
3. **The 2-phase field_simp pattern needs refinement** → Some goals don't close with `ring`

---

## 🔧 What I Tried

### Iteration 1: Applied User's Recipe Directly
- Added local shields inside each lemma → **Syntax error** (attribute not valid in tactic block)

### Iteration 2: Removed Inner Shields
- Realized section-level shields are sufficient → Build errors reduced slightly

### Iteration 3: Fixed Helper Lemmas
- `f_alt`: Changed from `rfl` to `unfold f; ring` → Fixed one error
- Fixed some unused Γtot terms → Linter warnings reduced

### Iteration 4: Fixed Derivative Computations
- Fix 3's derivative: Changed form to match `-(s - 2*M)` instead of `-s + 2*M`

**Result**: Still 16 errors, need more precise tactical guidance.

---

## 💡 Request for Exact Edits

Per your message:
> "If you'd like, I can draft the exact edits for each of the three stubborn lemmas (Fixes 1‑3) following the recipe above so you can paste them in—just say the word."

**Yes, please!** I would greatly appreciate the exact tactical edits for:

### Fix 1 (RiemannUp_r_trt_ext) - Lines 2048-2088
**Current errors**: Lines 2075 (simp no progress after shape)
**Issue**: After the hΓ_expand and hder' setup, the Γ rewrites + field_simp aren't closing

### Fix 2 (RiemannUp_t_θtθ_ext) - Lines 2114-2141
**Current errors**: Lines 2123 (unsolved goals in shape - derivative term), 2139 (no goals to solve)
**Issue**: Shape has `-deriv (fun t => 0) θ` that doesn't simplify, and extra tactic after closure

### Fix 3 (RiemannUp_r_θrθ_ext) - Lines 2143-2178
**Current errors**: Lines 2144 (unsolved goals after shape), 2153 (shape unsolved goals), 2164 (partially fixed)
**Issue**: Derivative form mismatch (partially fixed) + shape not closing

---

## 📝 Specific Questions

For each of Fixes 1-3, I need:

1. **Exact shape helper form** - What should the RHS of `have shape : ... = <what?>` be?
2. **Exact simp only lists** - Which Γtot terms to include/exclude?
3. **Derivative helper strategy** - For Fix 1 & 3, exact hΓ_expand / hder' forms
4. **Post-rw tactics** - Exact sequence after `rw [shape]` through the two-phase field_simp to `ring`

---

## 📂 Files Modified

**Main**:
- `GR/Riemann.lean` (lines 2019-2343)
  - Added normalization helpers
  - Applied uniform 2-phase pattern to all 7 lemmas
  - Removed unused Γtot terms (partial)
  - Fixed some derivative computations

**Documentation**:
- `GR/STATUS_OCT7_FINAL.md` (previous session)
- `GR/STATUS_ITERATION_REPORT.md` (this file)

---

## 🏗️ Current Build Status

```bash
cd /Users/quantmann/FoundationRelativity
lake build Papers.P5_GeneralRelativity.GR.Riemann
```

**Result**: 16 errors (down from 18 initially, but plateaued)

---

## 🎯 Next Steps

1. **Receive exact edits for Fixes 1-3 from Junior Professor**
2. **Apply those edits mechanically**
3. **Use the working pattern from Fixes 1-3 to fix Fixes 4-7**
4. **Build and verify 0 errors**
5. **Document successful patterns for future reference**

---

**Date**: October 7, 2025 (Continued Iteration)
**Session Focus**: Implementing uniform post-shape pipeline
**Progress**: Infrastructure in place, needs precise tactical edits
**Status**: 🟡 Awaiting exact edits for Fixes 1-3

---

## Appendix: Sample Error Output

```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:2123:35: unsolved goals
M r θ : ℝ
h_ext : Exterior M r θ
hr : r ≠ 0
⊢ -deriv (fun t => 0) θ + Γ_t_tr M r * Γ_r_θθ M r = Γ_t_tr M r * Γ_r_θθ M r

error: Papers/P5_GeneralRelativity/GR/Riemann.lean:2153:37: unsolved goals
M r θ : ℝ
h_ext : Exterior M r θ
hr : r ≠ 0
⊢ deriv (fun s => Γ_r_θθ M s) r - deriv (fun t => 0) θ +
    (Γ_r_rr M r * Γ_r_θθ M r - Γ_r_θθ M r * Γ_θ_rθ r) =
  -deriv (fun s => Γ_r_θθ M s) r + Γ_r_rr M r * Γ_r_θθ M r + Γ_r_θθ M r * Γ_θ_rθ r
```
