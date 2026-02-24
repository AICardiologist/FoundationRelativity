# DIAGNOSTIC: Step 3 + Step 4 Patches Failed

**Date**: November 4, 2025
**Status**: 🚨 BLOCKING - Both E1 and E15 fixes introduced new errors
**Error Count**: 18 → 21 errors (+3 errors introduced)

---

## Executive Summary

Paul's Step 3 (E1) and Step 4 (E15) patches were applied but **failed to compile**. Both patches assume that `ring` tactics can handle complex algebraic manipulations automatically, but in practice the expressions are too complex for `ring` to solve.

**Build Log**: `build_step3_step4_verified_nov4.txt`
**Result**: 21 errors (baseline was 18 after Step 2)

---

## Step 3 (E1) Failure Analysis

### Location
`regroup_left_sum_to_RiemannUp` lemma, `step4` proof (lines 6100-6123)

### Error
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:6115:72: unsolved goals
```

### Root Cause
The proof at lines 6116-6117 tries to use `ring` to prove a complex algebraic equality:
```lean
have hfold :
  f₁ ρ - f₂ ρ + f₃ ρ - f₄ ρ
    = g M a ρ r θ *
        ( dCoord Idx.r (fun r θ => Γtot M r θ ρ Idx.θ b) r θ
        - dCoord Idx.θ (fun r θ => Γtot M r θ ρ Idx.r b) r θ
        + sumIdx (fun lam =>
            Γtot M r θ ρ Idx.r lam * Γtot M r θ lam Idx.θ b
          - Γtot M r θ ρ Idx.θ lam * Γtot M r θ lam Idx.r b) ) := by
  simp [f₁, f₂, f₃, f₄, sub_eq_add_neg]
  ring  -- ❌ FAILS: ring cannot solve this goal
```

**Why `ring` fails**: After `simp` expands `f₁, f₂, f₃, f₄`, the resulting expression has `sumIdx` terms inside, which `ring` cannot handle (it only works on polynomial expressions over a ring, not indexed sums).

### Goal State at Failure
```lean
M r θ : ℝ
h_ext : Exterior M r θ
...
f1 : Idx → ℝ := fun k => dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ b) r θ * g M a k r θ
f2 : Idx → ℝ := fun k => dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r b) r θ * g M a k r θ
⊢ ... [complex goal with sumIdx terms]
```

The goal still contains references to `f₁, f₂, f₃, f₄` (the original `let` definitions) which need to be expanded and factored in a specific way.

---

## Step 4 (E15) Failure Analysis

### Location
`payload_cancel_all_flipped` lemma (lines 9294-9322)

### Errors
1. **Line 9308**: unsolved goals from `h_conv` proof
2. **Line 9319**: Type mismatch when applying `payload_cancel_all`
3. **Line 9322**: Type mismatch in final `simpa` step

### Root Cause 1: `ring` Cannot Prove Pointwise Equality (Line 9310)

The proof tries to use `ring` to reshape each summand:
```lean
have h_conv :
  sumIdx (fun e =>
     -(dCoord μ (fun r θ => g M e b r θ) r θ) * Γtot M r θ e ν a
   +  (dCoord ν (fun r θ => g M e b r θ) r θ) * Γtot M r θ e μ a
   -  (dCoord μ (fun r θ => g M a e r θ) r θ) * Γtot M r θ e ν b
   +  (dCoord ν (fun r θ => g M a e r θ) r θ) * Γtot M r θ e μ b)
  =
  sumIdx (fun e =>
     Γtot M r θ e ν a * dCoord μ (fun r θ => g M e b r θ) r θ
   - Γtot M r θ e μ a * dCoord ν (fun r θ => g M e b r θ) r θ
   + Γtot M r θ e ν b * dCoord μ (fun r θ => g M a e r θ) r θ
   - Γtot M r θ e μ b * dCoord ν (fun r θ => g M a e r θ) r θ) := by
  refine sumIdx_congr (fun e => ?_)
  ring  -- ❌ FAILS: ring cannot prove the pointwise equality
```

**Why `ring` fails**: The goal after `sumIdx_congr` is:
```lean
⊢ -(dCoord μ (fun r θ => g M e b r θ) r θ * Γtot M r θ e ν a) +
      (dCoord ν (fun r θ => g M e b r θ) r θ * Γtot M r θ e μ a - ...) + ...
    =
    dCoord μ (fun r θ => g M e b r θ) r θ * Γtot M r θ e ν a - ...
```

This requires:
1. Distributing negation: `-A * B = -(A * B)`
2. Commuting multiplication: `A * B = B * A`
3. Reassociating addition/subtraction

The `ring` tactic expects a simpler form and is failing on the complex nested structure with negation distribution.

### Root Cause 2: Type Mismatch with `payload_cancel_all` (Line 9319)

Even if `h_conv` were proven, the application of `payload_cancel_all` fails because the **shape** doesn't match. Looking at the type mismatch error:

**What `payload_cancel_all` expects** (unflipped form):
```lean
  sumIdx (fun ρ =>
    -Γtot M r θ ρ ν a * dCoord μ (fun r θ => g M ρ b r θ) r θ +
     Γtot M r θ ρ μ a * dCoord ν (fun r θ => g M ρ b r θ) r θ) +
  sumIdx (fun ρ =>
    -Γtot M r θ ρ μ a * dCoord ν (fun r θ => g M ρ b r θ) r θ +
     Γtot M r θ ρ ν a * dCoord μ (fun r θ => g M ρ b r θ) r θ) +
  ...
```

Note: `payload_cancel_all` has **4 separate `sumIdx` terms** that are added together.

**What the target has** (after attempting reshape):
```lean
sumIdx (fun e =>
   Γtot M r θ e ν a * dCoord μ (fun r θ => g M e b r θ) r θ
 - Γtot M r θ e μ a * dCoord ν (fun r θ => g M e b r θ) r θ
 + Γtot M r θ e ν b * dCoord μ (fun r θ => g M a e r θ) r θ
 - Γtot M r θ e μ b * dCoord ν (fun r θ => g M a e r θ) r θ)
```

Note: This is **a single `sumIdx` with 4 terms inside**, not 4 separate `sumIdx` added together.

**Architectural mismatch**: The existing `payload_cancel_all` expects the **split** form (4 separate sums added), but the flipped form has a **combined** form (1 sum with 4 terms inside).

---

## Lessons Learned

### 1. `ring` Has Limited Scope

**Limitation**: `ring` only works on polynomial expressions over a ring. It cannot handle:
- Indexed sums (`sumIdx`)
- Function applications like `dCoord Idx.r (fun r θ => ...)`
- Complex negation distribution patterns

**Application**: Both patches assumed `ring` would "just work" on complex expressions, but it's not powerful enough for these cases.

### 2. Architectural Compatibility Matters

**Lesson**: Even if you can prove a mathematical equality, you need to match the **exact shape** that existing lemmas expect.

**Application**: `payload_cancel_all` was designed for a **split** form (4 separate `sumIdx` added), but the flipped form is **combined** (1 `sumIdx` with 4 terms). Simply reshaping the inner terms isn't enough - you'd need to prove they're equal **after** splitting or combining.

### 3. "Drop-in" Patches Need More Infrastructure

**Observation**: Both patches assumed that existing Lean 4 tactics would handle the algebraic heavy lifting, but in practice:
- E1 needs explicit expansion of `f₁, f₂, f₃, f₄` followed by factoring
- E15 needs either:
  - (A) Infrastructure lemmas to split/combine `sumIdx` terms, or
  - (B) A completely rewritten `payload_cancel_all_flipped` that proves the result from scratch

---

## Recommended Next Steps

### Option 1: Request More Detailed Tactical Guidance

Ask Paul to provide **step-by-step** proof scripts that:
- Explicitly name each intermediate rewrite
- Don't rely on `ring` to solve complex goals
- Break down the proof into smaller, verifiable steps

### Option 2: Request Missing Infrastructure Lemmas

For E15, we may need:
- `sumIdx_split_add`: Prove `sumIdx (fun e => A e + B e) = sumIdx A + sumIdx B`
- `sumIdx_split_sub`: Prove `sumIdx (fun e => A e - B e) = sumIdx A - sumIdx B`
- Apply these repeatedly to convert the combined form to the split form

### Option 3: Revert and Try Alternative Approach

Revert to the baseline (18 errors) and ask Paul for a different strategy that:
- Uses existing infrastructure more directly
- Avoids complex `ring` applications
- Works with the architectural patterns already in place

---

## Current State

**Files Modified**:
- Riemann.lean: Lines 6100-6123 (E1 attempted fix)
- Riemann.lean: Lines 9294-9322 (E15 attempted fix)

**Build Logs**:
- `build_step3_step4_verified_nov4.txt`: 21 errors (18 baseline + 3 new)

**Git Status**: Modified but not committed (waiting for working fix)

---

## Request to Paul

**Need**: Either more detailed tactical proof scripts OR additional infrastructure lemmas to make the "drop-in" approach work.

**Specific Issues**:
1. **E1**: `ring` fails on complex expressions with `sumIdx` - need explicit step-by-step factoring
2. **E15**: Architectural mismatch between combined form (1 `sumIdx` with 4 terms) and split form (4 `sumIdx` added) - need splitting lemmas or alternative proof

**Alternative**: If these fixes are too complex for the "drop-in" approach, consider reverting to baseline and trying a different strategy for E1 and E15.

---

**CONCLUSION**: Both Step 3 and Step 4 patches failed due to overly optimistic assumptions about `ring` tactic capabilities and architectural compatibility. Need Paul's guidance on next steps.
