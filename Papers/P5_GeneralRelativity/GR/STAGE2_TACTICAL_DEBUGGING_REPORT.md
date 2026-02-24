# Stage 2 Tactical Debugging Report
**Date**: October 6, 2025 (Late Evening)
**To**: Junior Tactics Professor
**From**: AI Assistant (Claude Code)
**Subject**: Component Lemma Implementation - Debugging Log & Solutions

---

## Executive Summary

✅ **SUCCESS**: Implemented all 3 component lemmas + cancellation lemma
📉 **Progress**: Reduced from 6 sorries → 3 sorries (50% reduction)
🎯 **Diagonal case r.r**: Now proven using component cancellation

**Key Discovery**: The provided tactical patterns needed adjustment for how `simp [Γtot]` actually behaves in this file - specifically around derivative computation and function expansion order.

---

## What Was Implemented

### Component Lemmas (All ✅ Complete)
1. `RiemannUp_t_rtr_ext`: R^t_{rtr} = 2M/(r²(r-2M))
2. `RiemannUp_θ_rθr_ext`: R^θ_{rθr} = -M/(r²(r-2M))
3. `RiemannUp_φ_rφr_ext`: R^φ_{rφr} = -M/(r²(r-2M)) (φ-clone of θ)

### Cancellation Lemma (✅ Complete)
4. `Ricci_rr_cancellation`: Proves diagonal case R_rr = 0 via algebraic cancellation

### Zero Component Lemmas (Already Working)
- `RiemannUp_r_rrr_ext`, `RiemannUp_t_ttt_ext`, `RiemannUp_θ_θθθ_ext`, `RiemannUp_φ_φφφ_ext`
- All using clean one-liner pattern: `simpa using RiemannUp_mu_eq_nu`

---

## Debugging Journey

### Initial Attempt (FAILED)

**Provided proof pattern**:
```lean
unfold RiemannUp
simp [dCoord, sumIdx_expand, Γtot]

have hder := deriv_Γ_t_tr_at M r hr hf
rw [hder]; simp
simp [Γ_r_rr, Γ_t_tr]

field_simp [f, hr, hf, hrm, pow_two, sq]
ring
```

**Errors encountered**:
1. `Tactic 'rewrite' failed: Did not find an occurrence of the pattern`
2. `unsolved goals` after `ring`

### Root Cause Analysis

**Discovery**: After `simp [Γtot]`, the goal was already partially simplified:

```lean
-- Expected: deriv (fun s => Γ_t_tr M s) r
-- Actual:   deriv (Γ_r_rr M) r + (products of Γ_r_rr)
```

The `simp [Γtot]` step expanded `Γ_r_rr` **immediately**, changing the derivative term's structure so the `rw [hder]` pattern didn't match.

**Second issue**: The `field_simp [f, ...]` step left `f M r` unexpanded in the goal, causing `ring` to fail:

```lean
⊢ -(r * f M r * M ^ 2 * 4) + r ^ 2 * f M r * M * 2 = r ^ 2 * f M r ^ 2 * M * 2
```

---

## Solution 1: RiemannUp_t_rtr_ext

**Working proof** (lines 1953-1985):

```lean
lemma RiemannUp_t_rtr_ext
  (M r θ : ℝ) (h_ext : Exterior M r θ) :
  RiemannUp M r θ Idx.t Idx.r Idx.t Idx.r
    = 2 * M / (r^2 * (r - 2 * M)) := by
  classical
  have hr  : r ≠ 0     := Exterior.r_ne_zero h_ext
  have hf  : f M r ≠ 0 := Exterior.f_ne_zero h_ext
  have hrm : r - 2 * M ≠ 0 := by linarith [h_ext.hr_ex]

  -- Expand the definition
  unfold RiemannUp
  simp only [dCoord, sumIdx_expand]
  simp only [Γtot]

  -- Expand Γ_r_rr and Γ_t_tr directly (simp already did this)
  simp only [Γ_r_rr, Γ_t_tr]

  -- Substitute derivative lemmas explicitly
  have hder : deriv (fun s => M / (s ^ 2 * f M s)) r
      = - (2 * M) * (r * f M r + M) / (r ^ 4 * (f M r) ^ 2) :=
    deriv_Γ_t_tr_at M r hr hf

  have hder2 : deriv (fun s => -M / (s ^ 2 * f M s)) r
      = (2 * M) * (r * f M r + M) / (r ^ 4 * (f M r) ^ 2) :=
    deriv_Γ_r_rr_at M r hr hf

  simp only [hder, hder2]

  -- KEY FIX: Expand f BEFORE field_simp
  simp only [f]
  field_simp [hr, hrm]
  ring
```

**Key tactical changes**:
1. **`simp only` instead of `simp`**: More control over what gets simplified
2. **Explicit derivative lemmas**: Match the actual expanded form
3. **`simp only [f]` BEFORE `field_simp`**: Critical ordering - expand `f` first, then clear denominators
4. **Removed `hf` from `field_simp`**: Not needed after `f` is expanded
5. **Removed `pow_two, sq`**: Not necessary for this proof

---

## Solution 2: RiemannUp_θ_rθr_ext & RiemannUp_φ_rφr_ext

**Working proofs** (lines 1987-2009, 2011-2033):

These follow the exact pattern you provided and work perfectly:

```lean
lemma RiemannUp_θ_rθr_ext
  (M r θ : ℝ) (h_ext : Exterior M r θ) :
  RiemannUp M r θ Idx.θ Idx.r Idx.θ Idx.r
    = - M / (r^2 * (r - 2 * M)) := by
  classical
  have hr  : r ≠ 0     := Exterior.r_ne_zero h_ext
  have hf  : f M r ≠ 0 := Exterior.f_ne_zero h_ext
  have hrm : r - 2 * M ≠ 0 := by linarith [h_ext.hr_ex]

  -- Derivative of Γ^θ_{θr}(r) = 1/r
  have hder : deriv (fun s => Γ_θ_rθ s) r = - 1 / r^2 := by
    simpa [Γ_θ_rθ] using
      deriv_inv_general (fun s => s) r hr (differentiableAt_id r)

  -- Expand and simplify
  unfold RiemannUp
  simp [dCoord, sumIdx_expand, Γtot, hder, Γ_θ_rθ]

  -- Rewrite Γ^r_{rr} and normalize
  simp [Γ_r_rr, f]
  field_simp [hr, hf, hrm, pow_two, sq]
  ring
```

**Why these worked**: Simpler structure - the derivative of `1/r` and the cancellation pattern are cleaner, so the original tactical sequence works without modification.

---

## Solution 3: Ricci_rr_cancellation

**Working proof** (lines 3222-3249):

```lean
lemma Ricci_rr_cancellation
  (M r θ : ℝ) (h_ext : Exterior M r θ) :
  sumIdx (fun ρ => RiemannUp M r θ ρ Idx.r ρ Idx.r) = 0 := by
  classical
  have hr  : r ≠ 0     := Exterior.r_ne_zero h_ext
  have hf  : f M r ≠ 0 := Exterior.f_ne_zero h_ext
  have hrm : r - 2 * M ≠ 0 := by linarith [h_ext.hr_ex]

  -- Expand sumIdx to explicit 4-term sum and apply component lemmas
  simp only [sumIdx_expand]
  simp only [ RiemannUp_t_rtr_ext  M r θ h_ext
            , RiemannUp_r_rrr_ext  M r θ
            , RiemannUp_θ_rθr_ext  M r θ h_ext
            , RiemannUp_φ_rφr_ext  M r θ h_ext ]

  -- Algebraic simplification
  field_simp [hr, hrm]
  ring
```

**Key tactical changes from provided pattern**:
1. **`simp only` instead of `rw`**: The `rw` failed because indices were already bare (t, θ, φ instead of Idx.t, etc.) after `simp [sumIdx_expand]`
2. **Removed `simp only [f]`**: Already expanded by component lemmas
3. **Removed `hf, pow_two, sq` from `field_simp`**: Not needed for this algebraic goal

---

## Tactical Patterns Discovered

### Pattern 1: Function Expansion Order Matters

**WRONG**:
```lean
field_simp [f, hr, hf, hrm]  -- f unexpanded in goal
ring  -- FAILS
```

**RIGHT**:
```lean
simp only [f]           -- Expand f first
field_simp [hr, hrm]    -- Then clear denominators
ring                    -- SUCCESS
```

**Lesson**: When `field_simp` is given both a function definition (`f`) and nonzero hypotheses (`hf`), it may not expand the function, leaving it symbolic. Expand explicitly first.

### Pattern 2: simp vs. simp only

**Observation**: `simp [Γtot]` is too aggressive - it expands definitions we want to control.

**Solution**: Use `simp only [...]` with explicit lemma lists for fine-grained control.

### Pattern 3: Derivative Lemma Matching

**Challenge**: After `simp [Γtot]`, derivatives appear in expanded form:
```lean
deriv (Γ_r_rr M) r  -- NOT: deriv (fun s => Γ_t_tr M s) r
```

**Solution**: Define derivative lemmas with explicit lambda form:
```lean
have hder : deriv (fun s => M / (s ^ 2 * f M s)) r = ... :=
  deriv_Γ_t_tr_at M r hr hf
```

### Pattern 4: Component Lemma Application in sumIdx

**Challenge**: After `simp [sumIdx_expand]`, indices become bare and `rw` fails.

**Solution**: Use `simp only [component_lemma_1, component_lemma_2, ...]` to apply all rewrites atomically.

---

## Comparison: Provided vs. Working Proofs

### RiemannUp_t_rtr_ext

| Step | Provided Pattern | Working Pattern | Reason for Change |
|------|-----------------|----------------|-------------------|
| Unfold | `simp [dCoord, sumIdx_expand, Γtot]` | `simp only [dCoord, sumIdx_expand]; simp only [Γtot]` | More control |
| Derivative | `rw [hder]; simp` | `simp only [hder, hder2]` | Match expanded form |
| Γ subst | `simp [Γ_r_rr, Γ_t_tr]` | `simp only [Γ_r_rr, Γ_t_tr]` | Already expanded by simp |
| Algebra | `field_simp [f, hr, hf, hrm, ...]` | `simp only [f]; field_simp [hr, hrm]` | **Critical**: f expansion order |

### Ricci_rr_cancellation

| Step | Provided Pattern | Working Pattern | Reason for Change |
|------|-----------------|----------------|-------------------|
| Expand | `simp [sumIdx_expand]` | `simp only [sumIdx_expand]` | More control |
| Apply components | `rw [lemma1, lemma2, ...]` | `simp only [lemma1, lemma2, ...]` | Bare indices after simp |
| Algebra | `field_simp [f, hr, hf, hrm, ...]` | `field_simp [hr, hrm]` | f already expanded |

---

## Lessons for Future Component Lemmas

### Template for Non-Zero Components (like R^t_{rtr})

```lean
lemma RiemannUp_X_YZW_ext
  (M r θ : ℝ) (h_ext : Exterior M r θ) :
  RiemannUp M r θ Idx.X Idx.Y Idx.Z Idx.W = <value> := by
  classical
  have hr  : r ≠ 0     := Exterior.r_ne_zero h_ext
  have hf  : f M r ≠ 0 := Exterior.f_ne_zero h_ext
  have hrm : r - 2 * M ≠ 0 := by linarith [h_ext.hr_ex]

  unfold RiemannUp
  simp only [dCoord, sumIdx_expand]
  simp only [Γtot]
  simp only [Γ_<relevant_symbols>]

  -- If derivatives appear, substitute with explicit lambda form
  have hder : deriv (fun s => <explicit_form>) r = <value> := <lemma>
  simp only [hder]

  -- Expand f BEFORE field_simp
  simp only [f]
  field_simp [hr, hrm]
  ring
```

### Template for Simple Reciprocal Components (like R^θ_{rθr})

The provided pattern works perfectly - no changes needed!

```lean
lemma RiemannUp_X_YZW_ext
  (M r θ : ℝ) (h_ext : Exterior M r θ) :
  RiemannUp M r θ Idx.X Idx.Y Idx.Z Idx.W = <value> := by
  classical
  have hr  : r ≠ 0     := Exterior.r_ne_zero h_ext
  have hf  : f M r ≠ 0 := Exterior.f_ne_zero h_ext
  have hrm : r - 2 * M ≠ 0 := by linarith [h_ext.hr_ex]

  have hder : deriv (fun s => Γ_<symbol> s) r = <value> := by
    simpa [Γ_<symbol>] using deriv_inv_general ...

  unfold RiemannUp
  simp [dCoord, sumIdx_expand, Γtot, hder, Γ_<symbol>]
  simp [Γ_r_rr, f]
  field_simp [hr, hf, hrm, pow_two, sq]
  ring
```

---

## Current Status

### Completed (3 component lemmas + 1 cancellation)
- ✅ `RiemannUp_t_rtr_ext` (lines 1953-1985)
- ✅ `RiemannUp_θ_rθr_ext` (lines 1987-2009)
- ✅ `RiemannUp_φ_rφr_ext` (lines 2011-2033)
- ✅ `Ricci_rr_cancellation` (lines 3222-3249)
- ✅ Diagonal case `r.r` proven (line 3496)

### Remaining (3 sorries)
- ❌ Diagonal case `t.t` (line 3495)
- ❌ Diagonal case `θ.θ` (line 3497)
- ❌ Diagonal case `φ.φ` (line 3498)

**To complete these**: Need ~12 more component lemmas following the patterns above.

---

## Build Metrics

**Before**:
- Errors: 0
- Sorries: 6 (2 component lemmas + 4 diagonal cases)

**After**:
- Errors: 0
- Sorries: 3 (3 diagonal cases - r.r now complete!)
- Build time: ~same
- Warnings: Minor unused variable warnings only

---

## Recommendations for Remaining Work

### Immediate Next Steps (to complete tt, θθ, φφ)

1. **Implement missing component lemmas**:
   - R^r_{trt}, R^θ_{tθt}, R^φ_{tφt} (for tt diagonal)
   - R^t_{θtθ}, R^r_{θrθ}, R^φ_{θφθ} (for θθ diagonal)
   - R^t_{φtφ}, R^r_{φrφ}, R^θ_{φθφ} (for φφ diagonal)

2. **Pattern to use**:
   - t↔r components: Use RiemannUp_t_rtr_ext pattern (with f expansion fix)
   - θ/φ components: Use RiemannUp_θ_rθr_ext pattern (works as-is)

3. **Write cancellation lemmas**:
   ```lean
   lemma Ricci_tt_cancellation := ...  -- Clone Ricci_rr_cancellation
   lemma Ricci_θθ_cancellation := ...
   lemma Ricci_φφ_cancellation := ...
   ```

4. **Update diagonal cases**:
   ```lean
   case t.t => exact Ricci_tt_cancellation M r θ h_ext
   case θ.θ => exact Ricci_θθ_cancellation M r θ h_ext
   case φ.φ => exact Ricci_φφ_cancellation M r θ h_ext
   ```

### Estimated Effort
- **Per component lemma**: 5-10 minutes (now that pattern is known)
- **Per cancellation lemma**: 2 minutes (clone + adjust indices)
- **Total remaining**: ~12 components + 3 cancellations = **1-2 hours**

---

## Technical Insights

### Why field_simp Behaves Differently

`field_simp [f, hr, hf, hrm]` tries to:
1. Clear all denominators using nonzero hypotheses
2. Expand function definitions

But when both `f` (definition) and `hf : f M r ≠ 0` (hypothesis) are provided:
- Lean may keep `f M r` symbolic to use `hf` for denominator clearing
- This leaves `f M r` unexpanded in the goal
- `ring` fails because it can't normalize symbolic `f M r`

**Solution**: Separate the expansion from the clearing:
```lean
simp only [f]        -- Expand f to (1 - 2*M/r)
field_simp [hr, hrm] -- Clear denominators using r ≠ 0, r - 2*M ≠ 0
```

### Why simp [Γtot] Expands Too Much

The `Γtot` definition uses pattern matching on indices:
```lean
def Γtot (M r θ : ℝ) : Idx → Idx → Idx → ℝ := fun a b c =>
  classical
  if a = Idx.t ∧ b = Idx.t ∧ c = Idx.r then Γ_t_tr M r
  else if ... else 0
```

When `simp [Γtot]` sees concrete indices (like `Idx.t, Idx.r, Idx.t, Idx.r`), it:
1. Evaluates all the `if` conditions
2. Reduces to the branch value (e.g., `Γ_t_tr M r`)
3. **Immediately expands that value** using `Γ_t_tr` definition

This is too aggressive for proofs that want to control when Γ symbols expand.

**Solution**: Use `simp only [Γtot]` to stop after step 2, then explicitly control subsequent expansion.

---

## Conclusion

The provided tactical patterns are **fundamentally correct** - they just needed minor adjustments for this file's specific `simp` behavior:

1. **Function expansion order**: `simp only [f]` before `field_simp`
2. **Component lemma application**: `simp only [lemmas...]` instead of `rw`
3. **Derivative matching**: Explicit lambda forms in `have` statements

These are subtle but critical tactical refinements that make the difference between "unsolved goals" and "QED".

**All three component lemmas now compile with 0 errors**, and the r.r diagonal case is proven!

---

**Next session**: Scale this pattern to the remaining 12 component lemmas + 3 cancellations to achieve **0 sorries**.
