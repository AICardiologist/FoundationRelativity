# DIAGNOSTIC: Paul's Revised Patches Results

**Date**: November 4, 2025
**Build Log**: `build_step3_step4_revised_nov4.txt`
**Status**: ✅ E15 FIXED | ❌ E1 STILL FAILING

---

## Executive Summary

**E15 (payload_cancel_all_flipped)**: ✅ **SUCCESSFULLY FIXED**
- Paul's revised Patch B with `hpt` lemma worked perfectly
- No more "HasDistribNeg ℝ maximum recursion depth" error
- Error at line ~9364 is **ELIMINATED**

**E1 (regroup_left_sum_to_RiemannUp)**: ❌ **STILL FAILING**
- Paul's revised Patch A has an "unsolved goals" error at line 6111
- The `simp [f₁, f₂, sub_eq_add_neg, fold_sub_right]` tactic expands definitions too far
- After expansion, the goal shows `deriv` and raw metric definitions, not the expected algebraic form

**Error Count**: 22 errors (same as before, but different errors)

---

## E15 SUCCESS ANALYSIS

### What Worked

Paul's revised Patch B successfully eliminated E15 by:

1. **Introducing `hpt` lemma** (lines 9348-9360):
   ```lean
   have hpt :
     ∀ e,
       ( -(dCoord μ (fun r θ => g M e b r θ) r θ) * Γtot M r θ e ν a
       +   (dCoord ν (fun r θ => g M e b r θ) r θ) * Γtot M r θ e μ a
       -   (dCoord μ (fun r θ => g M a e r θ) r θ) * Γtot M r θ e ν b
       +   (dCoord ν (fun r θ => g M a e r θ) r θ) * Γtot M r θ e μ b )
       =
       ( Γtot M r θ e ν a * dCoord μ (fun r θ => g M e b r θ) r θ
       - Γtot M r θ e μ a * dCoord ν (fun r θ => g M e b r θ) r θ )
     + ( Γtot M r θ e ν b * dCoord μ (fun r θ => g M a e r θ) r θ
       - Γtot M r θ e μ b * dCoord ν (fun r θ => g M a e r θ) r θ ) := by
     intro e
     ring  -- ✅ Only ring at purely scalar level
   ```

2. **Using `hpt` under `sumIdx_congr`** (lines 9362-9375):
   ```lean
   have hunflip :
     sumIdx (fun e => -(dCoord ...) * Γtot ... + ...) =
     sumIdx (fun e => (Γtot ... * dCoord ... - ...) + (...)) := by
     refine sumIdx_congr (fun e => ?_)
     simpa using hpt e
   ```

3. **Simple split using `sumIdx_add_distrib`** (lines 9378-9392):
   ```lean
   have hsplit : ... := by
     simpa [sumIdx_add_distrib]  -- ✅ Clean split
   ```

### Key Innovation

The `hpt` lemma proves the pointwise equality using `ring` on **pure scalar expressions** (`∀ e, ...`), then lifts it to the `sumIdx` level using `sumIdx_congr`. This avoids:
- `simp` with multiple commutativity lemmas (which caused infinite loops)
- `ring` under `sumIdx` binders (which doesn't work)

**Result**: E15 is **completely eliminated** with no recursion errors or type mismatches.

---

## E1 FAILURE ANALYSIS

### Location
`regroup_left_sum_to_RiemannUp` lemma, `step4` proof, specifically `h12_r` at lines 6107-6114

### Error
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:6111:82: unsolved goals
⊢ deriv (fun s => Γtot M s θ ρ Idx.θ b) r *
    (match (motive := Idx → Idx → ℝ → ℝ → ℝ) a, ρ with
      | t, t => fun r _θ => -f M r
      | Idx.r, Idx.r => fun r _θ => (f M r)⁻¹
      | Idx.θ, Idx.θ => fun r _θ => r ^ 2
      | φ, φ => fun r θ => r ^ 2 * sin θ ^ 2
      ... ) = ...
```

### Root Cause

The proof at lines 6107-6114 uses:
```lean
have h12_r :
    f₁ ρ - f₂ ρ
      =
    ( dCoord Idx.r (fun r θ => Γtot M r θ ρ Idx.θ b) r θ
    - dCoord Idx.θ (fun r θ => Γtot M r θ ρ Idx.r b) r θ ) * g M a ρ r θ := by
  -- f₁ ρ and f₂ ρ are of the form (∂Γ) * g with g on the right.
  -- So (A*g) - (B*g) = (A - B) * g (deterministic fold).
  simp [f₁, f₂, sub_eq_add_neg, fold_sub_right]  -- ❌ OVER-EXPANDS
```

**Problem**: The `simp` tactic with `[f₁, f₂, ...]` expands:
1. `f₁ ρ` → `dCoord Idx.r (fun r θ => Γtot M r θ ρ Idx.θ b) r θ * g M a ρ r θ`
2. `dCoord` → `deriv (fun s => ...) r` (actual derivative definition)
3. `g M a ρ r θ` → big pattern match on metric components
4. Then tries to apply `fold_sub_right` and `sub_eq_add_neg`

After all these expansions, the goal has `deriv` terms and metric pattern matches, which don't match the expected form for `fold_sub_right` to close the goal.

### What `fold_sub_right` Expects

```lean
lemma fold_sub_right (a b c : ℝ) :
  a * c - b * c = (a - b) * c
```

It expects a goal of the form `(A * g) - (B * g) = (A - B) * g` where `A`, `B`, and `g` are already simple expressions.

But after `simp [f₁, f₂, ...]`, the goal has:
- `deriv (fun s => Γtot M s θ ρ Idx.θ b) r * (match a, ρ with ...) - ...`

The `match` expression for the metric and the `deriv` expansion prevent `fold_sub_right` from matching.

---

## Why E1 is Different from E15

**E15 Success**: Uses `hpt` lemma to prove pointwise equality with `ring`, then lifts via `sumIdx_congr`
**E1 Failure**: Tries to use `simp` with lemmas directly, but `simp` expands too far

**Key difference**: E15 proves the scalar equality **separately** in `hpt`, then applies it. E1 tries to prove everything in one `simp` call.

---

## Proposed Fix for E1

### Option A: Use Intermediate Lemma (Like E15's `hpt`)

```lean
have h12_r_pt :
  ∀ ρ,
    f₁ ρ - f₂ ρ
    =
    ( dCoord Idx.r (fun r θ => Γtot M r θ ρ Idx.θ b) r θ
    - dCoord Idx.θ (fun r θ => Γtot M r θ ρ Idx.r b) r θ ) * g M a ρ r θ := by
  intro ρ
  simp only [f₁, f₂]  -- Expand definitions without sub_eq_add_neg, fold_sub_right
  ring  -- Try pure ring

have h12_r :
    f₁ ρ - f₂ ρ = ... := h12_r_pt ρ
```

### Option B: Manual Rewriting

```lean
have h12_r :
    f₁ ρ - f₂ ρ
      =
    ( dCoord Idx.r (fun r θ => Γtot M r θ ρ Idx.θ b) r θ
    - dCoord Idx.θ (fun r θ => Γtot M r θ ρ Idx.r b) r θ ) * g M a ρ r θ := by
  unfold f₁ f₂  -- Manual unfold, no simp
  rw [fold_sub_right]  -- Explicit rewrite, not simp
```

### Option C: Use `calc` with Explicit Steps

```lean
have h12_r :
    f₁ ρ - f₂ ρ
      =
    ( dCoord Idx.r (fun r θ => Γtot M r θ ρ Idx.θ b) r θ
    - dCoord Idx.θ (fun r θ => Γtot M r θ ρ Idx.r b) r θ ) * g M a ρ r θ := by
  calc
    f₁ ρ - f₂ ρ
      = dCoord Idx.r (fun r θ => Γtot M r θ ρ Idx.θ b) r θ * g M a ρ r θ
        - dCoord Idx.θ (fun r θ => Γtot M r θ ρ Idx.r b) r θ * g M a ρ r θ := by
          simp only [f₁, f₂]
    _ = (dCoord Idx.r (fun r θ => Γtot M r θ ρ Idx.θ b) r θ
         - dCoord Idx.θ (fun r θ => Γtot M r θ ρ Idx.r b) r θ) * g M a ρ r θ := by
          exact fold_sub_right _ _ _
```

---

## Current File State

**Modified Lines**:
- E1 fix: Lines 6104-6173 (Paul's revised Patch A applied, but failing)
- E15 fix: Lines 9347-9417 (Paul's revised Patch B applied, working ✅)

**Build Logs**:
- `build_step3_step4_final_nov4.txt`: First build (before E15 fix) - 22 errors, both E1 and E15 failing
- `build_step3_step4_revised_nov4.txt`: After E15 fix - 22 errors, only E1 failing

**Git Status**: Modified but not committed (waiting for E1 fix)

---

## Request to Paul

**E15**: ✅ Complete success! The `hpt` lemma approach worked perfectly.

**E1**: ❌ Need help with the `h12_r` proof at line 6111.

**Specific issue**: The `simp [f₁, f₂, sub_eq_add_neg, fold_sub_right]` expands `dCoord` to `deriv` and the metric to a pattern match, leaving an unsolved goal that `fold_sub_right` cannot match.

**Question**: Should we use an intermediate pointwise lemma (like `hpt` in E15) to prove the equality for each `ρ` separately, then apply it? Or is there a better approach?

**Alternative**: Can provide the three options above (intermediate lemma, manual rewriting, or calc-based) for your review.

---

## Lessons Learned

1. **`simp` with definitional unfolding is unpredictable**: When `simp [f₁, f₂, ...]` is used, it may unfold more than expected, including internal definitions like `dCoord → deriv`.

2. **Intermediate lemmas work better for complex proofs**: E15's success shows that proving pointwise equalities separately (with `ring`) and lifting them with `sumIdx_congr` is more robust than trying to do everything in one tactic call.

3. **Explicit rewrites > `simp`**: For deterministic proofs, explicit `rw` or `calc` steps are more predictable than `simp` with multiple lemmas.

---

**CONCLUSION**: E15 is fully fixed and validated. E1 needs Paul's guidance on how to handle the over-expansion issue in the `h12_r` proof.
