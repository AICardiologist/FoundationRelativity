# Status Report - After Applying Finishers

**Date**: October 7, 2025
**Previous**: 8 errors
**Current**: 9 errors (new errors in helper lemmas + finishers)

---

## Summary

Applied all three normalizer helper lemmas and finishers as instructed by the Junior Professor. However, encountered new errors both in the helper lemmas themselves and in their application.

---

## Applied Changes ✅

1. **Added three helper lemmas** (lines 2047-2069):
   - `Mr_f_collapse` - Collapses `M*r*f` to polynomial
   - `Mr_f_linearize` - Linearizes `-(M*r*f)*k`
   - `collapse_r_sub_2M` - Collapses φφ diagonal cases

2. **Applied finishers**:
   - Fix 1: Added `Mr_f_linearize M r 2 hr` + `rw [h]; rfl`
   - Fix 2: Added `Mr_f_linearize M r 1 hr` + `rw [h]; rfl`
   - Fix 3: Added product normalization + double linearization
   - Fix 5: Added φφ collapse pattern
   - Fix 6: Added hfold calc + combine/collapse pattern
   - Fix 7: No changes (left as-is per guidance)

---

## New Errors (9 total)

### Helper Lemma Errors

#### Error 1: Mr_f_collapse (line 2052)
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:2052:2: No goals to be solved
```

**Lemma**:
```lean
lemma Mr_f_collapse (M r : ℝ) (hr : r ≠ 0) :
  M * r * f M r = M * r - 2 * M ^ 2 := by
  unfold f
  field_simp [hr]
  ring  -- ← ERROR: Goal already closed
```

**Fix**: Remove `ring` (goal closes after `field_simp [hr]`)

#### Error 2: collapse_r_sub_2M (line 2067)
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:2067:61: unsolved goals
M r k : ℝ
hsub : r - 2 * M ≠ 0
⊢ -(M * r * k * (-(M * 2) + r)⁻¹) + M ^ 2 * k * (-(M * 2) + r)⁻¹ * 2 = -(M * k)
```

**Lemma**:
```lean
lemma collapse_r_sub_2M (M r k : ℝ) (hsub : r - 2 * M ≠ 0) :
  ((-(M * r) + 2 * M ^ 2) * k) * (r - 2 * M)⁻¹ = -(M * k) := by
  field_simp [hsub]
  ring  -- ← ERROR: Goal has (-(M*2)+r)⁻¹ form, not (r-2*M)⁻¹
```

**Issue**: After `field_simp [hsub]`, the goal still has `(-(M*2)+r)⁻¹` which doesn't match the normalized `(r-2*M)⁻¹` pattern.

**Possible fix**: Add normalization:
```lean
lemma collapse_r_sub_2M (M r k : ℝ) (hsub : r - 2 * M ≠ 0) :
  ((-(M * r) + 2 * M ^ 2) * k) * (r - 2 * M)⁻¹ = -(M * k) := by
  have : -(M * 2) + r = r - 2 * M := by ring
  field_simp [hsub]
  simp only [this]
  ring
```

### Finisher Application Errors

#### Error 3: Fix 1 finisher (line 2108)
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:2108:10: Tactic `rfl` failed: The left-hand side
  -(M * r * 2) + M ^ 2 * 4
is not definitionally equal to the right-hand side
  -(M * r * 2) + M ^ 2 * (2 * 2)
```

**Current code**:
```lean
have h := Mr_f_linearize M r 2 hr
rw [h]; rfl  -- ← ERROR: 4 ≠ (2*2) definitionally
```

**Issue**: `Mr_f_linearize` produces `M^2 * (2*k)` = `M^2 * (2*2)` = `M^2 * 4`, but Lean doesn't see `4` and `(2*2)` as definitionally equal without `ring`.

**Fix**: Use `ring` instead of `rfl`:
```lean
have h := Mr_f_linearize M r 2 hr
rw [h]; ring
```

#### Error 4: Fix 2 finisher (line 2157)
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:2157:6: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  -(M * r * f M r * ?m.48)
```

**Current code**:
```lean
have h := Mr_f_linearize M r 1 hr
rw [h]; rfl
```

**Issue**: The pattern from `Mr_f_linearize M r 1 hr` doesn't match the actual goal form.

#### Error 5: Fix 3 finisher (line 2197)
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:2197:31: Tactic `rewrite` failed: Did not find an occurrence of the pattern
```

Similar pattern matching issue.

#### Error 6: Fix 4 (line 2203)
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:2203:57: unsolved goals
```

(Existing error from before - Fix 4 wasn't touched with finishers)

#### Error 7-9: Fix 5, 6 finisher errors
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:2261:2: Tactic `assumption` failed
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:2317:6: Type mismatch
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:2320:2: Tactic `assumption` failed
```

Issues with the `simpa` tactics in Fix 5 and Fix 6 finishers.

---

## Root Cause Analysis

### Issue 1: Helper Lemma Definition Mismatch

The provided helper lemmas assume specific algebraic forms that might not match after our `unfold f` and `field_simp`. Specifically:

1. **Mr_f_collapse**: Closes after `field_simp [hr]`, doesn't need `ring`
2. **collapse_r_sub_2M**: The form `(-(M*2)+r)⁻¹` appears instead of `(r-2*M)⁻¹`

### Issue 2: Finisher Pattern Matching

The finishers use `rw [h]; rfl` expecting definitional equality, but:
- `M^2 * 4` vs `M^2 * (2*2)` aren't definitionally equal
- The actual goal forms after `ring` don't match the patterns in the helper lemmas

### Issue 3: Our `f` Definition

Our definition:
```lean
def f (M r : ℝ) : ℝ := 1 - 2 * M / r
```

After `unfold f` and `field_simp [hr]`, this might produce different intermediate forms than expected.

---

## Proposed Fixes

### Fix Helper Lemmas

1. **Mr_f_collapse**: Remove trailing `ring`
   ```lean
   lemma Mr_f_collapse (M r : ℝ) (hr : r ≠ 0) :
     M * r * f M r = M * r - 2 * M ^ 2 := by
     unfold f
     field_simp [hr]
   ```

2. **collapse_r_sub_2M**: Add normalization step
   ```lean
   lemma collapse_r_sub_2M (M r k : ℝ) (hsub : r - 2 * M ≠ 0) :
     ((-(M * r) + 2 * M ^ 2) * k) * (r - 2 * M)⁻¹ = -(M * k) := by
     have : -(M * 2) + r = r - 2 * M := by ring
     simp only [this]
     field_simp [hsub]
     ring
   ```

### Fix Finishers

Replace `rw [h]; rfl` with `rw [h]; ring` in all finishers, since the goals aren't definitionally equal but are algebraically equal.

---

## Questions for Junior Professor

1. **Helper lemma forms**: Do the helpers need adjustment for our specific `f` definition `1 - 2*M/r`?

2. **Normalization**: Should we add a step to normalize `(-(M*2)+r)` to `(r-2*M)` in the helpers or before calling them?

3. **Definitional vs algebraic equality**: Should finishers use `ring` instead of `rfl` when the LHS and RHS are only algebraically (not definitionally) equal?

4. **Alternative approach**: Would it be simpler to adjust the goal statements to have `f` pre-expanded, avoiding these normalization issues?

---

## Build Command

```bash
cd /Users/quantmann/FoundationRelativity
lake build Papers.P5_GeneralRelativity.GR.Riemann
```

**Current result**: 9 errors

---

## Next Steps

1. Fix the two helper lemmas (remove ring from Mr_f_collapse, fix collapse_r_sub_2M)
2. Replace `rfl` with `ring` in all finishers
3. Verify pattern matching in Fix 2-3 finishers
4. Test build

---

**Status**: 🟡 Helpers and finishers applied but need minor adjustments
