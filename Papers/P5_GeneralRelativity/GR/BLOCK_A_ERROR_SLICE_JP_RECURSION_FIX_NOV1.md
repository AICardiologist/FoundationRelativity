# Block A Error Slice - After JP's Recursion Fix - November 1, 2025

**Date**: November 1, 2025
**Build**: `build_jp_recursion_fix_nov1.txt`
**Total Errors**: 24 (down from 26)
**Block A Errors**: 8 (down from 10)
**Errors Eliminated**: 2 recursion errors ✅

---

## Executive Summary

✅ **SUCCESS**: JP's recursion fix (`rw [neg_mul_right₀]; exact`) completely eliminated the two typeclass synthesis infinite recursion errors at lines 8771 and 9033.

**What Remains**: 8 errors in Block A, all appearing to be cascade errors from issues in the contraction equality application.

---

## Error Progression

| Round | Errors | Block A | Notes |
|-------|--------|---------|-------|
| Composed equalities | 24 | 10 | After `.trans` approach |
| Negation normalizers | 26 | 10 | Added recursion errors |
| Recursion fix | **24** | **8** | Recursion errors eliminated ✅ |

**Net Improvement**: 26 → 24 errors (7.7% reduction)
**Block A Improvement**: 10 → 8 errors (20% reduction)

---

## Remaining Block A Errors (8 total)

### b-branch Errors (Lines 8709-8837)

```
error: 8709:39: unsolved goals
error: 8788:33: unsolved goals
error: 8804:8:  Type mismatch: After simplification
error: 8808:12: Tactic `rewrite` failed: Did not find an occurrence of the pattern
error: 8837:65: unsolved goals
```

### a-branch Errors (Lines 8978-9050)

```
error: 8978:39: unsolved goals
error: 9011:10: Type mismatch ⚠️ PRIMARY ERROR
error: 9050:33: unsolved goals
```

---

## Detailed Error Analysis

### ⚠️ PRIMARY ERROR: Line 9011 (a-branch h2 contraction)

**Location**: Inside `core_as_sum_a`, step `h2` (contraction)

**Error Message**:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9011:10: Type mismatch
  Eq.symm (sumIdx_contract_g_left M r θ a X)
has type
  g M a a r θ * X a = sumIdx fun d => g M d a r θ * X d
but is expected to have type
  X a * g M a a r θ = sumIdx fun ρ => g M a ρ r θ * X ρ
```

**Code Context** (lines 9007-9011):
```lean
-- (2) contract Σ_ρ g_{aρ}·X ρ ↔ X a · g_{aa}
have h2 :
  X a * g M a a r θ
    = sumIdx (fun ρ => g M a ρ r θ * X ρ) :=
  (sumIdx_contract_g_left M r θ a X).symm  -- ← ERROR HERE
```

**Analysis**:

The `sumIdx_contract_g_left` lemma provides:
```
g M a a r θ * X a = sumIdx fun d => g M d a r θ * X d
```

But we need:
```
X a * g M a a r θ = sumIdx fun ρ => g M a ρ r θ * X ρ
```

**Two mismatches**:
1. **LHS**: Factors reversed (`g * X` vs `X * g`)
2. **RHS**: Indices reversed inside sum (`g M d a` vs `g M a ρ`)

**Hypothesis**: Need to apply both `mul_comm` (for factor order) AND `g_symm_indices` (for index order) before using the contraction lemma.

---

### Error 2: Line 8709 (b-branch unsolved goals)

**Location**: Inside the outer `have` for b-branch contraction delta structure

**Error Message**:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8709:39: unsolved goals
M r θ : ℝ
h_ext : Exterior M r θ
hθ : sin θ ≠ 0
μ ν a b : Idx
bb_core : ℝ := sumIdx fun ρ => g M ρ b r θ * (...)
h_bb_core : bb_core = sumIdx fun ρ => g M ρ b r θ * (...)
rho_core_b : ℝ := sumIdx fun ρ => g M ρ ρ r θ * (...)
```

**Code Context** (lines 8690-8709):
```lean
have h_insert_delta_for_b :
  sumIdx (fun ρ =>
    - ( ( dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ
         - dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ
         + sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
         - sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) )
        * g M ρ b r θ ) )
  =
  sumIdx (fun ρ =>
    - ( ( dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ
         - dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ
         + sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
         - sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) )
        * g M ρ b r θ )
    * (if ρ = b then 1 else 0)) := by
  classical
  -- 2) Contraction for the b-branch (clean, direction-aware)
  -- ...
  rw [core_as_sum_b_mul]  -- LINE 8709: unsolved goals
```

**Hypothesis**: The `rw [core_as_sum_b_mul]` doesn't fully close the goal because the target still needs the Kronecker delta `(if ρ = b then 1 else 0)` to be inserted, but `core_as_sum_b_mul` only rewrites the LHS without the delta.

---

### Error 3: Line 8788 (b-branch scalar_finish unsolved goals)

**Error**: `unsolved goals` at the `intro ρ` in `scalar_finish`

**Code Context** (lines 8776-8790):
```lean
/- 3) Final scalar packaging -/
have scalar_finish :
  ∀ ρ,
    ( -(dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ) * g M ρ b r θ
      +  (dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ) * g M ρ b r θ )
    +  ( g M ρ b r θ *
          ( sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
           -sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) ) )
    =
      - ( ( dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ
           - dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ
           + sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
           - sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) )
          * g M ρ b r θ ) := by
  intro ρ  -- LINE 8788: unsolved goals
  ring
```

**Hypothesis**: Cascade from line 8709 - the surrounding proof context is in a bad state from the failed `rw [core_as_sum_b_mul]`.

---

### Error 4: Line 8804 (b-branch calc type mismatch)

**Error**: `Type mismatch: After simplification`

**Code Context** (lines 8793-8804):
```lean
/- 4) Assemble to get hb_partial with rho_core_b -/
calc
  (sumIdx B_b)
- sumIdx (fun ρ => (Γtot M r θ ρ μ a) * (nabla_g M r θ ν ρ b))
+ sumIdx (fun ρ => (Γtot M r θ ρ ν a) * (nabla_g M r θ μ ρ b))
    = sumIdx (fun ρ =>
          - ( dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ
             - dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ
             + sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
             - sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) )
           * g M ρ b r θ) := by
    simp only [nabla_g, RiemannUp, sub_eq_add_neg]
    simpa [payload_cancel, ΓΓ_block] using (sumIdx_congr scalar_finish)  -- LINE 8804
```

**Full Error**:
```
has type
  (sumIdx fun i => -(g M b i r θ * dCoord μ (fun r θ => Γtot M r θ i ν a) r θ)) +
        g M b b r θ * dCoord ν (fun r θ => Γtot M r θ b μ a) r θ + ...
but is expected to have type
  (sumIdx B_b + ((-sumIdx fun k => -(Γtot M r θ k μ a * ...)) + ...
```

**Hypothesis**: The `simpa` application of `scalar_finish` produces the wrong shape because `scalar_finish` failed to prove at line 8788.

---

### Error 5: Line 8808 (b-branch rewrite failed)

**Error**: `Tactic 'rewrite' failed: Did not find an occurrence of the pattern`

**Code Context** (lines 8805-8819):
```lean
_   = - sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ)
    + rho_core_b := by
  simp only [h_rho_core_b]
  rw [← core_as_sum_b, ← sumIdx_add_distrib]  -- LINE 8808: rw fails
  apply sumIdx_congr; intro ρ
  simp only [RiemannUp]
  split_ifs with h_rho_eq_b
  · -- ρ = b case
    subst h_rho_eq_b
    simp only [h_bb_core]
    rw [← scalar_finish_bb]
    ring
  · -- ρ ≠ b case: Kronecker δ = 0
    simp
    ring
```

**Pattern Not Found**:
```
sumIdx fun ρ =>
  -(((dCoord μ ... - sumIdx ...) * g M ρ b r θ) * if ρ = b then 1 else 0
```

**Target**:
```
(sumIdx fun ρ => -((dCoord μ ... - sumIdx ...) * g M ρ b r θ)) = ...
```

**Analysis**: The target doesn't have the Kronecker delta factor `(if ρ = b then 1 else 0)`. The rewrite is looking for `core_as_sum_b` which presumably includes the delta, but it's not present in the current goal.

---

### Error 6: Line 8837 (b-branch calc unsolved goals)

**Error**: `unsolved goals` in the calc chain

**Code Context**: Same calc chain as Error 5, but at the final step.

**Hypothesis**: Cascade from the failed rewrite at line 8808.

---

### Error 7: Line 8978 (a-branch unsolved goals)

**Error**: `unsolved goals` (symmetric to b-branch line 8709)

**Code Context** (lines 8959-8978):
```lean
have h_insert_delta_for_a :
  sumIdx (fun ρ =>
    - ( ( dCoord μ (fun r θ => Γtot M r θ ρ ν b) r θ
         - dCoord ν (fun r θ => Γtot M r θ ρ μ b) r θ
         + sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν b)
         - sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ b) )
        * g M a ρ r θ ) )
  =
  sumIdx (fun ρ =>
    - ( ( dCoord μ (fun r θ => Γtot M r θ ρ ν b) r θ
         - dCoord ν (fun r θ => Γtot M r θ ρ μ b) r θ
         + sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν b)
         - sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ b) )
        * g M a ρ r θ )
    * (if ρ = a then 1 else 0)) := by
  classical
  -- 2) Contraction for the a-branch (clean, direction-aware)
  -- ...
  rw [core_as_sum_a_mul]  -- LINE 8978: unsolved goals
```

**Hypothesis**: Same as b-branch - the `rw` doesn't insert the Kronecker delta.

---

### Error 8: Line 9050 (a-branch scalar_finish unsolved goals)

**Error**: `unsolved goals` (symmetric to b-branch line 8788)

**Code Context** (lines 9038-9052):
```lean
/- 3) Final scalar packaging -/
have scalar_finish :
  ∀ ρ,
    ( -(dCoord μ (fun r θ => Γtot M r θ ρ ν b) r θ) * g M a ρ r θ
      +  (dCoord ν (fun r θ => Γtot M r θ ρ μ b) r θ) * g M a ρ r θ )
    +  ( g M a ρ r θ *
          ( sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν b)
           -sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ b) ) )
    =
      - ( ( dCoord μ (fun r θ => Γtot M r θ ρ ν b) r θ
           - dCoord ν (fun r θ => Γtot M r θ ρ μ b) r θ
           + sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν b)
           - sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ b) )
          * g M a ρ r θ ) := by
  intro ρ  -- LINE 9050: unsolved goals
  ring
```

**Hypothesis**: Cascade from line 8978 (a-branch symmetric to b-branch).

---

## Pattern Analysis

### Primary Issue: Line 9011 (a-branch contraction signature)

The `sumIdx_contract_g_left` lemma has the wrong signature for our needs:

**Available**:
```lean
g M a a r θ * X a = sumIdx fun d => g M d a r θ * X d
```

**Needed**:
```lean
X a * g M a a r θ = sumIdx fun ρ => g M a ρ r θ * X ρ
```

**Two transformations needed**:
1. **Factor commutation**: `g * X` → `X * g` (need `mul_comm`)
2. **Index symmetry**: `g M d a` → `g M a d` (need `g_symm_indices`)

### Secondary Issue: Kronecker Delta Insertion (Lines 8709, 8978)

The goals expect:
```lean
sumIdx (fun ρ => E ρ * (if ρ = b then 1 else 0))
```

But `core_as_sum_b_mul` only provides:
```lean
sumIdx (fun ρ => E ρ)
```

**Missing step**: Need to explicitly insert `* 1` and then rewrite to `* (if ρ = b then 1 else 0)` using a delta insertion lemma.

### Cascade Errors

Lines 8788, 8804, 8808, 8837, 9050 are all downstream from the primary issues:
- b-branch cascades from line 8709 (delta insertion failure)
- a-branch cascades from line 8978 (delta insertion failure) and line 9011 (contraction signature)

---

## Code Neighborhoods

### b-branch Contraction Neighborhood (Lines 8690-8820)

```lean
-- Outer goal: insert Kronecker delta into the sum
have h_insert_delta_for_b :
  sumIdx (fun ρ => -((...) * g M ρ b r θ))
  = sumIdx (fun ρ => -((...) * g M ρ b r θ) * (if ρ = b then 1 else 0)) := by
  classical

  -- Define X (clean scalar core)
  set X : Idx → ℝ := fun ρ => -(dCoord μ ... - dCoord ν ... + sumIdx ... - sumIdx ...)

  -- Step 1: Build core_as_sum_b via .trans chain
  have core_as_sum_b :
    -((...)) * g M b b r θ = sumIdx (fun ρ => g M ρ b r θ * X ρ) := by
    -- h1: freeze b-slice
    -- h2: contract
    -- h3: swap indices
    -- h4: commute factors
    exact h1.trans (h2.trans (h3.trans h4))

  -- Step 2: Repackage with outer negation
  have core_as_sum_b_mul :
    -(((...)) * g M b b r θ) = sumIdx (fun ρ => g M ρ b r θ * X ρ) := by
    rw [neg_mul_right₀]; exact core_as_sum_b  -- ✅ RECURSION FIX WORKS

  rw [core_as_sum_b_mul]  -- ⚠️ LINE 8709: UNSOLVED GOALS - needs delta insertion

/- 3) Final scalar packaging -/
have scalar_finish : ∀ ρ, ... = ... := by
  intro ρ  -- ⚠️ LINE 8788: UNSOLVED GOALS (cascade from 8709)
  ring

/- 4) Assemble to get hb_partial with rho_core_b -/
calc
  (sumIdx B_b) - sumIdx ... + sumIdx ...
    = sumIdx (fun ρ => -(dCoord μ ... - sumIdx ...) * g M ρ b r θ) := by
      simp only [nabla_g, RiemannUp, sub_eq_add_neg]
      simpa [payload_cancel, ΓΓ_block] using (sumIdx_congr scalar_finish)  -- ⚠️ LINE 8804: TYPE MISMATCH
  _   = - sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ) + rho_core_b := by
      simp only [h_rho_core_b]
      rw [← core_as_sum_b, ← sumIdx_add_distrib]  -- ⚠️ LINE 8808: REWRITE FAILED - pattern includes delta
      apply sumIdx_congr; intro ρ
      simp only [RiemannUp]
      split_ifs with h_rho_eq_b
      · subst h_rho_eq_b
        simp only [h_bb_core]
        rw [← scalar_finish_bb]
        ring
      · simp
        ring  -- ⚠️ LINE 8837: UNSOLVED GOALS (cascade)
```

### a-branch Contraction Neighborhood (Lines 8959-9070)

```lean
-- Outer goal: insert Kronecker delta into the sum
have h_insert_delta_for_a :
  sumIdx (fun ρ => -((...) * g M a ρ r θ))
  = sumIdx (fun ρ => -((...) * g M a ρ r θ) * (if ρ = a then 1 else 0)) := by
  classical

  -- Define X (clean scalar core)
  set X : Idx → ℝ := fun ρ => -(dCoord μ ... - dCoord ν ... + sumIdx ... - sumIdx ...)

  -- Step 1: Build core_as_sum_a via .trans chain
  have core_as_sum_a :
    -((...)) * g M a a r θ = sumIdx (fun ρ => g M ρ a r θ * X ρ) := by
    classical
    -- (1) freeze the a-slice
    have h1 : -((...)) * g M a a r θ = X a * g M a a r θ := by
      simpa [X]

    -- (2) contract Σ_ρ g_{aρ}·X ρ ↔ X a · g_{aa}
    have h2 :
      X a * g M a a r θ = sumIdx (fun ρ => g M a ρ r θ * X ρ) :=
      (sumIdx_contract_g_left M r θ a X).symm  -- ⚠️ LINE 9011: TYPE MISMATCH - signature wrong!

    -- (3) swap indices under Σ to get g_{ρa}
    have h3 :
      sumIdx (fun ρ => g M a ρ r θ * X ρ) = sumIdx (fun ρ => g M ρ a r θ * X ρ) := by
      refine sumIdx_congr (fun ρ => ?_)
      simpa using congrArg (fun t => t * X ρ) (g_symm_indices M r θ a ρ)

    exact h1.trans (h2.trans h3)  -- ⚠️ CAN'T BUILD - h2 fails!

  -- Step 2: Repackage with outer negation
  have core_as_sum_a_mul :
    -(((...)) * g M a a r θ) = sumIdx (fun ρ => g M ρ a r θ * X ρ) := by
    rw [neg_mul_right₀]; exact core_as_sum_a  -- ⚠️ CAN'T USE - core_as_sum_a fails!

  rw [core_as_sum_a_mul]  -- ⚠️ LINE 8978: UNSOLVED GOALS

/- 3) Final scalar packaging -/
have scalar_finish : ∀ ρ, ... = ... := by
  intro ρ  -- ⚠️ LINE 9050: UNSOLVED GOALS (cascade from 8978)
  ring

/- 4) Assemble calc chain -/
-- (Similar cascade errors as b-branch)
```

---

## Questions for JP

### Q1: a-branch Contraction Signature (Line 9011)

The `sumIdx_contract_g_left` lemma provides:
```lean
g M a a r θ * X a = sumIdx fun d => g M d a r θ * X d
```

But we need:
```lean
X a * g M a a r θ = sumIdx fun ρ => g M a ρ r θ * X ρ
```

**Question**: Should we:
1. Add intermediate steps to apply `mul_comm` and `g_symm_indices` before using the contraction lemma?
2. Create a variant lemma `sumIdx_contract_g_left_comm` that has the factors pre-commuted?
3. Use a different contraction approach entirely for the a-branch?

### Q2: Kronecker Delta Insertion (Lines 8709, 8978)

The outer `have` goals expect the sum to include `* (if ρ = b then 1 else 0)`, but `core_as_sum_b_mul` doesn't have this factor.

**Question**: Should we:
1. Add a step after `rw [core_as_sum_b_mul]` to explicitly insert `* 1` and then rewrite to the delta?
2. Modify `core_as_sum_b_mul` to include the delta factor in its RHS?
3. Use `convert` instead of `rw` to handle the structural mismatch?

### Q3: b-branch vs a-branch Symmetry

The b-branch and a-branch should be symmetric, but the a-branch has an additional error (line 9011) that the b-branch doesn't have.

**Question**: Why does `sumIdx_contract_g_right` work for b-branch but `sumIdx_contract_g_left` fails for a-branch? Is there a difference in how the lemmas are stated?

---

## Summary

✅ **Recursion fix successful**: Both typeclass synthesis errors eliminated
⚠️ **Primary blocker**: Line 9011 - `sumIdx_contract_g_left` signature mismatch
⚠️ **Secondary blocker**: Lines 8709, 8978 - Kronecker delta insertion needed
📊 **Cascade errors**: 5 errors (lines 8788, 8804, 8808, 8837, 9050) likely to resolve once primary/secondary blockers fixed

---

**Prepared by**: Claude Code (Lean 4 Assistant)
**Date**: November 1, 2025
**Build**: `build_jp_recursion_fix_nov1.txt`
**Status**: Recursion errors eliminated ✅, contraction signature mismatch remains
**Progress**: 26 → 24 errors (7.7% reduction overall, 20% in Block A)

---

**End of Report**
