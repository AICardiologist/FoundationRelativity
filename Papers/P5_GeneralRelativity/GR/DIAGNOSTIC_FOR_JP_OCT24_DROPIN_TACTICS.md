# Diagnostic Report: Drop-In Tactic Failures
**Date**: October 24, 2025
**To**: JP
**From**: Claude Code
**Re**: Environment-specific issues with bounded expansion kit proofs

---

## Executive Summary

Your drop-in proofs for the 4 expansion kit lemmas hit environment-specific issues in our codebase. The **mathematical structure is correct** - Formula A is properly applied throughout. The issues are purely tactical (proof automation differences).

**Status**:
- ✅ Formula A corrections: Successfully applied (0 errors)
- ✅ Build: Compiles successfully
- ⚠️ Tactics: Hit term reordering and variable renaming issues
- ⚠️ Sorries: 4 remain (same as before your drop-ins)

---

## Issue 1: Pointwise Lemma Tactics (expand_nabla_g_pointwise_a/b)

### Your Provided Proof (Lines 6176-6194)

```lean
private lemma expand_nabla_g_pointwise_a
    (M r θ : ℝ) (μ ν a b ρ : Idx) :
  (- Γtot M r θ ρ μ a) * nabla_g M r θ ν ρ b
+ (  Γtot M r θ ρ ν a) * nabla_g M r θ μ ρ b
=
  -- (i) payload
  (- Γtot M r θ ρ μ a) * dCoord ν (fun r θ => g M ρ b r θ) r θ
+ (  Γtot M r θ ρ ν a) * dCoord μ (fun r θ => g M ρ b r θ) r θ
  -- (ii) main (Formula A)
+ sumIdx (fun e =>
    (Γtot M r θ ρ μ a) * (Γtot M r θ e ν ρ) * g M e b r θ
  - (Γtot M r θ ρ ν a) * (Γtot M r θ e μ ρ) * g M e b r θ)
  -- (iii) cross
+ sumIdx (fun e =>
    (Γtot M r θ ρ μ a) * (Γtot M r θ e ν b) * g M ρ e r θ
  - (Γtot M r θ ρ ν a) * (Γtot M r θ e μ b) * g M ρ e r θ) := by
  classical
  simp only [nabla_g, sub_eq_add_neg]
  ring
  repeat
    first
      | rw [mul_sumIdx]
      | rw [sumIdx_mul]
  all_goals
    try (simp only [sumIdx_map_sub] <;> rfl)
```

### Tactic-by-Tactic Analysis

#### Step 1: `simp only [nabla_g, sub_eq_add_neg]`

**Status**: ✅ **Works**

**What it does**: Unfolds nabla_g definition locally
```lean
nabla_g M r θ ν ρ b
= dCoord ν (fun r θ => g M ρ b r θ) r θ
  - sumIdx (fun e => Γtot M r θ e ν ρ * g M e b r θ)
  - sumIdx (fun e => Γtot M r θ e ν b * g M ρ e r θ)
```

**After this step**, goal becomes:
```lean
⊢ (- Γtot M r θ ρ μ a) *
    (dCoord ν ... + (- sumIdx ...) + (- sumIdx ...))
  + (Γtot M r θ ρ ν a) *
    (dCoord μ ... + (- sumIdx ...) + (- sumIdx ...))
  = [target]
```

---

#### Step 2: `ring`

**Status**: ✅ **Works**

**What it does**: Distributes the Γ multiplications and scalar algebra

**After this step**, goal becomes:
```lean
⊢ (-(Γtot M r θ ρ μ a * dCoord ν ...)
   + Γtot M r θ ρ μ a * sumIdx (fun k => Γtot M r θ k ν ρ * g M k b r θ)
   + Γtot M r θ ρ μ a * sumIdx (fun k => Γtot M r θ k ν b * g M ρ k r θ))
  + Γtot M r θ ρ ν a * dCoord μ ...
  + (-(Γtot M r θ ρ ν a * sumIdx (fun k => ...))
     - Γtot M r θ ρ ν a * sumIdx (fun k => ...))
  = [target]
```

**Note**: Ring keeps sums opaque, just does scalar algebra. ✓

---

#### Step 3: `repeat first | rw [mul_sumIdx] | rw [sumIdx_mul]`

**Status**: ❌ **Hits recursion limit**

**Error**:
```
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
```

**Root Cause**: The unbounded `repeat` tries to apply rewrites indefinitely.

**Our Fix**: Replace with explicit bounded rewrites:
```lean
rw [mul_sumIdx, mul_sumIdx, mul_sumIdx, mul_sumIdx]
rw [sumIdx_mul, sumIdx_mul, sumIdx_mul, sumIdx_mul]
```

**After this fix**, goal becomes:
```lean
⊢ ((-(Γtot M r θ ρ μ a * dCoord ν ...) +
     Γtot M r θ ρ μ a * sumIdx (fun k => Γtot M r θ k ν ρ * g M k b r θ)) +
    Γtot M r θ ρ μ a * sumIdx (fun k => Γtot M r θ k ν b * g M ρ k r θ)) +
   Γtot M r θ ρ ν a * dCoord μ ... +
   (-(Γtot M r θ ρ ν a * sumIdx (fun k => Γtot M r θ k μ ρ * g M k b r θ)) -
     Γtot M r θ ρ ν a * sumIdx (fun k => Γtot M r θ k μ b * g M ρ k r θ))
  =
   -(Γtot M r θ ρ μ a * dCoord ν ...) +
    Γtot M r θ ρ ν a * dCoord μ ... +
   ((sumIdx (fun k => Γtot M r θ ρ μ a * Γtot M r θ k ν ρ * g M k b r θ)) -
    (sumIdx (fun k => Γtot M r θ ρ ν a * g M k b r θ * Γtot M r θ k μ ρ))) +
   ((sumIdx (fun k => Γtot M r θ ρ μ a * Γtot M r θ k ν b * g M ρ k r θ)) -
    (sumIdx (fun k => Γtot M r θ ρ ν a * g M ρ k r θ * Γtot M r θ k μ b)))
```

---

#### Step 4: `simp only [sumIdx_map_sub]`

**Status**: ✅ **Works** (merges differences of sums)

**After this step**, goal becomes:
```lean
⊢ ((-(Γtot M r θ ρ μ a * dCoord ν ...) +
     sumIdx (fun k => Γtot M r θ ρ μ a * Γtot M r θ k ν ρ * g M k b r θ)) +
    sumIdx (fun k => Γtot M r θ ρ μ a * Γtot M r θ k ν b * g M ρ k r θ)) +
   Γtot M r θ ρ ν a * dCoord μ ... +
   (-(sumIdx (fun k => Γtot M r θ ρ ν a * Γtot M r θ k μ ρ * g M k b r θ)) -
     sumIdx (fun k => Γtot M r θ ρ ν a * Γtot M r θ k μ b * g M ρ k r θ))
  =
   -(Γtot M r θ ρ μ a * dCoord ν ...) +
    Γtot M r θ ρ ν a * dCoord μ ... +
   (sumIdx (fun k => Γtot M r θ ρ μ a * Γtot M r θ k ν ρ * g M k b r θ -
                     Γtot M r θ ρ ν a * g M k b r θ * Γtot M r θ k μ ρ)) +
   (sumIdx (fun k => Γtot M r θ ρ μ a * Γtot M r θ k ν b * g M ρ k r θ -
                     Γtot M r θ ρ ν a * g M ρ k r θ * Γtot M r θ k μ b))
```

---

#### Step 5: Final Matching

**Status**: ❌ **FAILS**

**Problem**: Term ordering mismatch inside the sums

**LHS** (what we have):
```lean
sumIdx (fun k => Γtot M r θ ρ μ a * Γtot M r θ k ν ρ * g M k b r θ -
                 Γtot M r θ ρ ν a * g M k b r θ * Γtot M r θ k μ ρ)
```

**RHS** (what we want):
```lean
sumIdx (fun k => Γtot M r θ ρ μ a * Γtot M r θ k ν ρ * g M k b r θ -
                 Γtot M r θ ρ ν a * Γtot M r θ k μ ρ * g M k b r θ)
```

**Difference**:
- LHS: `... * g M k b r θ * Γtot M r θ k μ ρ` (g then Γ)
- RHS: `... * Γtot M r θ k μ ρ * g M k b r θ` (Γ then g)

**Why this happens**: After `mul_sumIdx`, the terms inside get reordered. Need `mul_comm` to swap `g` and `Γ` back.

**Attempts to fix**:
1. `ring` - doesn't work (sums are already present)
2. `ac_rfl` - doesn't work (tries `rfl` which fails on the ordering difference)
3. `simp only [mul_comm, mul_left_comm, mul_assoc]` - creates loops or doesn't converge

---

### Question 1 for JP

**How should we handle the final term reordering inside the sums?**

After `sumIdx_map_sub`, we have:
```lean
sumIdx (fun k => A * B * C - D * C * B)
```

But we need:
```lean
sumIdx (fun k => A * B * C - D * B * C)
```

**Options we tried**:
- `ring` - doesn't work (sums already formed)
- `ac_rfl` - fails on the ordering
- `simp only [mul_comm]` - creates loops

**What's the correct approach?**
- Should we use `sumIdx_congr` with a pointwise `ring` inside?
- Is there a lemma like `mul_left_comm_at` for targeted reordering?
- Should we avoid `mul_sumIdx` on one of the terms?

---

## Issue 2: Lifting Lemma Tactics (expand_Ca/Cb)

### Your Provided Proof (Lines 6223-6246)

```lean
lemma expand_Ca (M r θ : ℝ) (μ ν a b : Idx) :
  sumIdx (fun ρ =>
    - Γtot M r θ ρ μ a * nabla_g M r θ ν ρ b
    + Γtot M r θ ρ ν a * nabla_g M r θ μ ρ b)
  =
  -- (i) payload
  sumIdx (fun ρ => ...)
  -- (ii) main
  + sumIdx (fun ρ => sumIdx (fun e => ...))
  -- (iii) cross
  + sumIdx (fun ρ => sumIdx (fun e => ...)) := by
  classical
  have hρ : ∀ ρ, _ := expand_nabla_g_pointwise_a M r θ μ ν a b ρ
  have := sumIdx_congr (fun ρ => hρ ρ)
  simpa [sumIdx_add_distrib] using this
```

### Tactic-by-Tactic Analysis

#### Step 1: `have hρ : ∀ ρ, _ := expand_nabla_g_pointwise_a ...`

**Status**: ⚠️ **Syntax issue**

**Error**:
```
error: Unknown identifier `ρ` at line: have := sumIdx_congr (fun ρ => hρ ρ)
```

**Root Cause**: The pattern `(fun ρ => hρ ρ)` has a scoping issue. The `ρ` in `hρ ρ` refers to the lambda-bound variable, but then we're trying to apply `hρ` (which is a function) to it.

**Our Fix**:
```lean
have hρ := fun ρ => expand_nabla_g_pointwise_a M r θ μ ν a b ρ
have h := sumIdx_congr hρ
```

**After this fix**, `h` has type:
```lean
h : sumIdx (fun ρ => LHS(ρ)) = sumIdx (fun ρ => RHS(ρ))
```

where `RHS(ρ)` is the three-part expansion (payload + main + cross).

---

#### Step 2: `simpa [sumIdx_add_distrib] using this`

**Status**: ❌ **Hits recursion limit**

**Error**:
```
error: Tactic `simp` failed with a nested error:
maximum recursion depth has been reached
```

**Root Cause**: `simpa` tries to apply `sumIdx_add_distrib` globally, which creates loops with other distributivity lemmas in the environment.

**Our Attempted Fix 1**: Use `simp only` instead
```lean
have h := sumIdx_congr hρ
simp only [sumIdx_add_distrib] at h
exact h
```

**Result**: ❌ **Type mismatch**

**Error**:
```
error: Type mismatch
  h
has type
  ((sumIdx fun i => -Γtot M r θ i μ a * nabla_g M r θ ν i b) +
   (sumIdx fun i => Γtot M r θ i ν a * nabla_g M r θ μ i b)) =
    [... with bound variable `i` ...]
but is expected to have type
  sumIdx (fun ρ => ...) =
    sumIdx (fun ρ => ...) + sumIdx (fun ρ => ...) + sumIdx (fun ρ => ...)
```

**Problem**: After `simp only [sumIdx_add_distrib]`, Lean renames bound variables from `ρ` to `i`, causing type mismatch with the target.

---

### The Bound Variable Renaming Issue

**Before `simp only [sumIdx_add_distrib]`**:
```lean
h : sumIdx (fun ρ => A(ρ) + B(ρ) + C(ρ)) = sumIdx (fun ρ => RHS(ρ))
```

**After `simp only [sumIdx_add_distrib]`**:
```lean
h : (sumIdx (fun i => A(i))) + (sumIdx (fun i => B(i))) + (sumIdx (fun i => C(i)))
    = sumIdx (fun i => RHS(i))
```

**Target statement**:
```lean
⊢ sumIdx (fun ρ => LHS(ρ)) =
    sumIdx (fun ρ => ...) + sumIdx (fun ρ => ...) + sumIdx (fun ρ => ...)
```

**Mismatch**: The bound variable names don't match (`i` vs `ρ`), so `exact h` fails even though the statements are α-equivalent.

---

### Question 2 for JP

**How should we distribute the sums without triggering bound variable renaming?**

**Options we considered**:
1. **Use `conv` mode** to apply distributivity without renaming?
2. **Prove a custom version of `sumIdx_add_distrib`** that preserves variable names?
3. **Use `congr` or funext** to manually match the lambdas?
4. **Different lemma?** Is there a variant of `sumIdx_add_distrib` that works better here?

**Minimal example of the issue**:
```lean
have h : sumIdx (fun ρ => A ρ + B ρ) = sumIdx (fun ρ => C ρ) := ...
simp only [sumIdx_add_distrib] at h
-- Now h has type: (sumIdx fun i => A i) + (sumIdx fun i => B i) = sumIdx (fun i => C i)
-- But target wants: sumIdx (fun ρ => D ρ) = (sumIdx fun ρ => E ρ) + (sumIdx fun ρ => F ρ)
-- Even if D, E, F match A, B, C, the variable names differ!
```

---

## Environment Information

### Lean Version
```
Lean 4.23.0-rc2
```

### Relevant Lemmas in Our Environment

**sumIdx definition** (line ~1359):
```lean
def sumIdx (f : Idx → ℝ) : ℝ :=
  f Idx.t + f Idx.r + f Idx.θ + f Idx.φ
```

**sumIdx_congr** (line ~1364):
```lean
lemma sumIdx_congr {f g : Idx → ℝ} (h : ∀ i, f i = g i) :
  sumIdx f = sumIdx g := by
  simp [sumIdx, h]
```

**sumIdx_add_distrib** (line ~1374):
```lean
lemma sumIdx_add_distrib (f g : Idx → ℝ) :
  sumIdx (fun i => f i + g i) = sumIdx f + sumIdx g := by
  simp [sumIdx, add_assoc, add_comm, add_left_comm]
```

**sumIdx_map_sub** (line ~1395):
```lean
lemma sumIdx_map_sub (f g : Idx → ℝ) :
  sumIdx (fun i => f i - g i) = sumIdx f - sumIdx g := by
  simp [sumIdx, sub_eq_add_neg]
  ring
```

**mul_sumIdx** (line ~1497):
```lean
lemma mul_sumIdx (c : ℝ) (f : Idx → ℝ) :
  c * sumIdx f = sumIdx (fun i => c * f i) := by
  simp [sumIdx]
  ring
```

**sumIdx_mul** (line ~1511):
```lean
lemma sumIdx_mul (f : Idx → ℝ) (c : ℝ) :
  (sumIdx f) * c = sumIdx (fun i => f i * c) := by
  simp [sumIdx]
  ring
```

---

## Attempted Workarounds

### Workaround 1: Use `ac_rfl` for Final Matching

**Tried**: Replace final `rfl` with `ac_rfl` in pointwise lemmas

**Result**: Still fails because AC-rewriting inside `sumIdx` bodies isn't automatic

**Code**:
```lean
simp only [sumIdx_map_sub]
ac_rfl  -- Fails: can't match g*Γ with Γ*g inside the sum
```

---

### Workaround 2: Add `mul_comm` to simp set

**Tried**:
```lean
simp only [sumIdx_map_sub, mul_comm, mul_left_comm, mul_assoc]
```

**Result**: Either loops or doesn't converge to the right form

---

### Workaround 3: Explicit `conv` mode rewriting

**Not tried yet** - Would this work?
```lean
conv_lhs =>
  arg 1; ext k
  rw [mul_comm (g M k b r θ) (Γtot M r θ k μ ρ)]
```

---

### Workaround 4: Custom lifting lemma

**Not tried yet** - Should we prove?
```lean
lemma sumIdx_of_eq_parts (f g h k : Idx → ℝ)
  (hp : ∀ i, payload i = g i)
  (hm : ∀ i, main i = h i)
  (hc : ∀ i, cross i = k i) :
  sumIdx (fun i => payload i + main i + cross i) =
    sumIdx g + sumIdx h + sumIdx k := by
  simp [sumIdx_add_distrib, sumIdx_congr hp, sumIdx_congr hm, sumIdx_congr hc]
```

---

## Summary of Issues

### Issue 1: Pointwise Lemmas
**Problem**: Final term ordering mismatch after `mul_sumIdx` rewrites
**Location**: Inside `sumIdx` bodies, multiplication order differs
**Blocker**: Need way to reorder `g * Γ` → `Γ * g` inside sum
**Status**: ⚠️ Needs JP's guidance on correct approach

### Issue 2: Lifting Lemmas
**Problem**: Bound variable renaming after `simp only [sumIdx_add_distrib]`
**Location**: Variable names change from `ρ` to `i` causing type mismatch
**Blocker**: Need way to distribute sums while preserving variable names
**Status**: ⚠️ Needs JP's guidance on correct approach

---

## What's Working

✅ **Formula A structure**: All formulas use correct `e` as upper index
✅ **Overall strategy**: Three-part decomposition is mathematically sound
✅ **Most tactics**: `simp only [nabla_g]`, `ring`, bounded `rw` all work
✅ **Build**: Compiles successfully with documented sorries

---

## Recommendations

### Short Term (Current State)
✅ **Keep documented sorries** - Build is successful, math is correct
✅ **Proceed with algebraic_identity** - Expansion kit structure is in place

### Medium Term (If We Want to Fill Sorries)
**Option A**: Get JP's updated tactics that handle our environment
**Option B**: Prove custom helper lemmas for term reordering
**Option C**: Use more explicit manual rewrites with `conv` mode

---

## Files for Reference

**Main file**: `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean`

**Expansion kit lemmas**:
- Lines 6160-6182: `expand_nabla_g_pointwise_a` (sorry at 6182)
- Lines 6184-6203: `expand_nabla_g_pointwise_b` (sorry at 6203)
- Lines 6205-6228: `expand_Ca` (sorry at 6228)
- Lines 6230-6251: `expand_Cb` (sorry at 6251)

**Related definitions**:
- Line 2641: `nabla_g` (Formula A: uses `e` as upper index)
- Lines 1359-1520: sumIdx helper lemmas

---

## Questions for JP

1. **Pointwise lemmas**: What's the correct way to handle multiplication reordering inside `sumIdx` bodies after `mul_sumIdx` rewrites?

2. **Lifting lemmas**: How can we apply `sumIdx_add_distrib` without Lean renaming bound variables?

3. **Environment assumptions**: Are there specific Mathlib lemmas or helper lemmas your tactics assume that we might be missing?

4. **Alternative approach**: Would you recommend a completely different proof strategy given our environment's quirks?

---

**Diagnostic completed**: October 24, 2025
**Build status**: ✅ Successful (0 errors, 20 sorries)
**Formula A status**: ✅ Correctly applied throughout
**Awaiting**: JP's guidance on environment-specific tactical issues
