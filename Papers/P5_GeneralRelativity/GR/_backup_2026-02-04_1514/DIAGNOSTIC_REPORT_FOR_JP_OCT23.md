# Diagnostic Report: algebraic_identity Implementation Issues
**Date**: October 23, 2025
**For**: JP (no VS Code access - this is a complete standalone report)
**Status**: ❌ Tactical mismatches block implementation
**Current Build**: ✅ 0 errors, 14 sorries (with diagnostic structure)

---

## Executive Summary

Your Step 1 patterns are **mathematically correct** but encounter **3 tactical/technical issues** when applied to our codebase:

1. **Differentiability hypotheses** - `discharge_diff` tactic expects facts in context, but they're not there
2. **Product rule expansion** - `dCoord_sumIdx` + `simp` doesn't automatically expand products
3. **Type inference** - After chaining lemmas, Lean's simplifier changes sum representations

**Good news**: `hPμ` (the first step) **compiles successfully** ✅
**Blocker**: `hPμ_expand` needs explicit differentiability proofs we don't have lemmas for

---

## Section 1: Our Actual Lemma Signatures

### 1.1 `dCoord_sub_of_diff` (Line 1004)

**Actual signature**:
```lean
@[simp] lemma dCoord_sub_of_diff (μ : Idx) (f g : ℝ → ℝ → ℝ) (r θ : ℝ)
    (hf_r : DifferentiableAt_r f r θ ∨ μ ≠ Idx.r)
    (hg_r : DifferentiableAt_r g r θ ∨ μ ≠ Idx.r)
    (hf_θ : DifferentiableAt_θ f r θ ∨ μ ≠ Idx.θ)
    (hg_θ : DifferentiableAt_θ g r θ ∨ μ ≠ Idx.θ) :
    dCoord μ (fun r θ => f r θ - g r θ) r θ =
    dCoord μ f r θ - dCoord μ g r θ
```

**Key point**: Requires 4 differentiability hypotheses with **disjunction** (`∨ μ ≠ Idx.r`)

---

### 1.2 `dCoord_sumIdx` (Line 1127)

**Actual signature**:
```lean
@[simp] lemma dCoord_sumIdx (μ : Idx) (F : Idx → ℝ → ℝ → ℝ) (r θ : ℝ)
    (hF_r : ∀ i, DifferentiableAt_r (F i) r θ ∨ μ ≠ Idx.r)
    (hF_θ : ∀ i, DifferentiableAt_θ (F i) r θ ∨ μ ≠ Idx.θ) :
  dCoord μ (fun r θ => sumIdx (fun i => F i r θ)) r θ =
  sumIdx (fun i => dCoord μ (fun r θ => F i r θ) r θ)
```

**Key point**: Pushes derivative through sum, but **does NOT apply product rule inside**

**What it gives**:
```lean
dCoord μ (fun r θ => sumIdx (fun ρ => Γ * g)) r θ
= sumIdx (fun ρ => dCoord μ (fun r θ => Γ * g) r θ)  -- NOT expanded yet!
```

**What we need after**:
```lean
sumIdx (fun ρ => dCoord μ Γ * g + Γ * dCoord μ g)  -- Product rule applied
```

---

### 1.3 `dCoord_mul_of_diff` (Line 1026)

**Actual signature**:
```lean
@[simp] lemma dCoord_mul_of_diff (μ : Idx) (f g : ℝ → ℝ → ℝ) (r θ : ℝ)
    (hf_r : DifferentiableAt_r f r θ ∨ μ ≠ Idx.r)
    (hg_r : DifferentiableAt_r g r θ ∨ μ ≠ Idx.r)
    (hf_θ : DifferentiableAt_θ f r θ ∨ μ ≠ Idx.θ)
    (hg_θ : DifferentiableAt_θ g r θ ∨ μ ≠ Idx.θ) :
    dCoord μ (fun r θ => f r θ * g r θ) r θ =
    dCoord μ f r θ * g r θ + f r θ * dCoord μ g r θ
```

**Key point**: Product rule, requires 4 differentiability hypotheses

---

### 1.4 `discharge_diff` Tactic (Line 919)

**Actual behavior**:
```lean
syntax "discharge_diff" : tactic

macro_rules
| `(tactic| discharge_diff) =>
  `(tactic| (
      first
      -- Strategy 1a: Prove left side of disjunction
      | { left; discharge_diff }  -- Recursive
      -- Strategy 1b: Prove right side (mismatch)
      | { right; simp [Idx.noConfusion] }
      -- Strategy 1c: Apply combinator lemmas
      | { apply DifferentiableAt_r_mul_of_cond <;> discharge_diff }
      ...
      -- Strategy 2: After unfolding, use base facts
      | {
          (try { unfold DifferentiableAt_r DifferentiableAt_θ })
          first
          | { apply DifferentiableAt.mul <;> discharge_diff }
          ...
          | { apply g_differentiable_r_ext; assumption }  -- Needs h_ext in context
          | { apply Γtot_differentiable_r_ext; assumption }  -- Needs h_ext in context
          ...
        }
      ))
```

**Key behaviors**:
1. Tries to **recursively** discharge differentiability
2. Falls back to lemmas like `g_differentiableAt r_ext`, `Γtot_differentiable_r_ext`
3. These lemmas use **`assumption`** to find `h_ext : Exterior M r θ` in context
4. **Works fine** for simple expressions (g, Γ)
5. **Fails** for compound expressions like `dCoord ν g` or `sumIdx (Γ * g)`

---

## Section 2: What Your Patterns Expect

### Your Step 1A Pattern (hPμ_expand):

```lean
have hPμ_expand :
  dCoord μ (fun r θ =>
    dCoord ν (fun r θ => g M a b r θ) r θ
    - sumIdx (fun ρ => Γtot M r θ ρ ν a * g M ρ b r θ)
    - sumIdx (fun ρ => Γtot M r θ ρ ν b * g M a ρ r θ)) r θ
  =
    dCoord μ (fun r θ => dCoord ν (fun r θ => g M a b r θ) r θ) r θ
    - dCoord μ (fun r θ => sumIdx (fun ρ => Γtot M r θ ρ ν a * g M ρ b r θ)) r θ
    - dCoord μ (fun r θ => sumIdx (fun ρ => Γtot M r θ ρ ν b * g M a ρ r θ)) r θ := by
  have h₁ := dCoord_sub_of_diff μ
    (fun r θ => dCoord ν (fun r θ => g M a b r θ) r θ)
    (fun r θ => sumIdx (fun ρ => Γtot M r θ ρ ν a * g M ρ b r θ))
    r θ (by discharge_diff) (by discharge_diff)  -- ❌ These fail
    (by discharge_diff) (by discharge_diff)      -- ❌ These fail
  ...
```

**What happens**: `discharge_diff` tries to prove:
```lean
DifferentiableAt_r (fun r θ => dCoord ν (fun r θ => g M a b r θ) r θ) r θ
```

But we **don't have** a lemma like `dCoord_g_differentiable_r` that applies here!

---

### Your Step 1A Pattern (hPμ_sum1):

```lean
have hPμ_sum1 :
  dCoord μ (fun r θ => sumIdx (fun ρ => Γtot M r θ ρ ν a * g M ρ b r θ)) r θ
  =
  sumIdx (fun ρ =>
    dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ * g M ρ b r θ
  + Γtot M r θ ρ ν a * dCoord μ (fun r θ => g M ρ b r θ) r θ) := by
  refine dCoord_sumIdx μ (fun ρ r θ => Γtot M r θ ρ ν a * g M ρ b r θ) r θ ?_ ?_
  · intro ρ; exact (DifferentiableAt_r_mul_of_cond _ _ r θ μ (by discharge_diff) (by discharge_diff))
  · intro ρ; exact (DifferentiableAt_θ_mul_of_cond _ _ r θ μ (by discharge_diff) (by discharge_diff))
  simp [dCoord_mul_of_diff, (by discharge_diff), (by discharge_diff)]  -- ❌ Doesn't expand as expected
```

**What happens**:
1. `dCoord_sumIdx` succeeds ✅ and gives:
   ```lean
   sumIdx (fun ρ => dCoord μ (fun r θ => Γtot M r θ ρ ν a * g M ρ b r θ) r θ)
   ```

2. `simp [dCoord_mul_of_diff, ...]` tries to apply product rule inside sum

3. **Problem**: `dCoord_mul_of_diff` expects 4 differentiability hypotheses but we only provided `(by discharge_diff)`

4. The pattern `(by discharge_diff)` **doesn't work inside simp** - simp can't execute tactics!

---

## Section 3: The Exact Blockers

### Blocker 1: Missing Differentiability Lemmas

We need but **don't have**:

```lean
lemma dCoord_g_differentiable_r (M r θ : ℝ) (h_ext : Exterior M r θ) (ν a b : Idx) :
  DifferentiableAt_r (fun r θ => dCoord ν (fun r θ => g M a b r θ) r θ) r θ

lemma dCoord_g_differentiable_θ (M r θ : ℝ) (h_ext : Exterior M r θ) (ν a b : Idx) :
  DifferentiableAt_θ (fun r θ => dCoord ν (fun r θ => g M a b r θ) r θ) r θ

lemma sumIdx_Γg_differentiable_r (M r θ : ℝ) (h_ext : Exterior M r θ) (ν a b : Idx) :
  DifferentiableAt_r (fun r θ => sumIdx (fun ρ => Γtot M r θ ρ ν a * g M ρ b r θ)) r θ

lemma sumIdx_Γg_differentiable_θ (M r θ : ℝ) (h_ext : Exterior M r θ) (ν a b : Idx) :
  DifferentiableAt_θ (fun r θ => sumIdx (fun ρ => Γtot M r θ ρ ν a * g M ρ b r θ)) r θ
```

**Why these are missing**: We have differentiability for **base expressions** (g, Γ) but not for **compound expressions** (dCoord g, sumIdx Γ*g)

---

### Blocker 2: Product Rule Inside Sum Doesn't Auto-Expand

After `dCoord_sumIdx`, we have:
```lean
sumIdx (fun ρ => dCoord μ (fun r θ => Γtot M r θ ρ ν a * g M ρ b r θ) r θ)
```

Your pattern tries:
```lean
simp [dCoord_mul_of_diff, (by discharge_diff), (by discharge_diff)]
```

**Problem**: `simp` can't execute `(by discharge_diff)` - tactics don't work as simp arguments!

**What we need**: Either:
- **Option A**: Pre-prove the differentiability facts as separate `have` statements
- **Option B**: Use a custom tactic that applies product rule + discharges differentiability
- **Option C**: Use `conv` mode to manually apply `dCoord_mul_of_diff` with explicit proofs

---

### Blocker 3: Type Mismatches After Chaining

After:
```lean
simpa [hPμ_sum1, hPμ_sum2] using hPμ.trans hPμ_expand
```

**Expected type**:
```lean
dCoord μ (fun r θ => nabla_g M r θ ν a b) r θ =
  ... (expanded form with sumIdx)
```

**Actual type** (after simplification):
```lean
dCoord μ (fun r θ => nabla_g M r θ ν a b) r θ =
  ... (sumIdx collapsed to specific indices)
```

**Root cause**: Lean's simplifier is more aggressive than expected, evaluating `sumIdx` to `g M t + g M r + g M θ + g M φ`

---

## Section 4: Working vs. Failing Examples

### ✅ WORKS: hPμ (Simple Simp)

```lean
have hPμ :
  dCoord μ (fun r θ => nabla_g M r θ ν a b) r θ
  =
  dCoord μ (fun r θ =>
    dCoord ν (fun r θ => g M a b r θ) r θ
    - sumIdx (fun ρ => Γtot M r θ ρ ν a * g M ρ b r θ)
    - sumIdx (fun ρ => Γtot M r θ ρ ν b * g M a ρ r θ)) r θ := by
  simp [nabla_g, sub_eq_add_neg]
```

**Why it works**: Just unfolds definitions, no differentiation needed

---

### ❌ FAILS: hPμ_expand (Needs Differentiability)

```lean
have hPμ_expand :
  dCoord μ (fun r θ =>
    dCoord ν (fun r θ => g M a b r θ) r θ
    - sumIdx (fun ρ => Γtot M r θ ρ ν a * g M ρ b r θ)
    - sumIdx (fun ρ => Γtot M r θ ρ ν b * g M a ρ r θ)) r θ
  =
    dCoord μ (fun r θ => dCoord ν (fun r θ => g M a b r θ) r θ) r θ
    - dCoord μ (fun r θ => sumIdx (fun ρ => Γtot M r θ ρ ν a * g M ρ b r θ)) r θ
    - dCoord μ (fun r θ => sumIdx (fun ρ => Γtot M r θ ρ ν b * g M a ρ r θ)) r θ := by
  have h₁ := dCoord_sub_of_diff μ
    (fun r θ => dCoord ν (fun r θ => g M a b r θ) r θ)
    (fun r θ => sumIdx (fun ρ => Γtot M r θ ρ ν a * g M ρ b r θ))
    r θ (by discharge_diff) (by discharge_diff)  -- ❌ FAILS HERE
    (by discharge_diff) (by discharge_diff)
  ...
```

**Error message**:
```
Tactic `assumption` failed

Goal:
  DifferentiableAt_r (fun r θ => dCoord ν (fun r θ => g M a b r θ) r θ) r θ
```

**Why it fails**: `discharge_diff` tries all its strategies, eventually reaches `assumption`, but `h_ext` alone isn't enough to prove differentiability of `dCoord ν g`

---

### ❌ FAILS: hPμ_sum1 Final Simp

```lean
have hPμ_sum1 :
  dCoord μ (fun r θ => sumIdx (fun ρ => Γtot M r θ ρ ν a * g M ρ b r θ)) r θ
  =
  sumIdx (fun ρ =>
    dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ * g M ρ b r θ
  + Γtot M r θ ρ ν a * dCoord μ (fun r θ => g M ρ b r θ) r θ) := by
  refine dCoord_sumIdx μ (fun ρ r θ => Γtot M r θ ρ ν a * g M ρ b r θ) r θ ?_ ?_
  · intro ρ; exact (DifferentiableAt_r_mul_of_cond _ _ r θ μ (by discharge_diff) (by discharge_diff))
  · intro ρ; exact (DifferentiableAt_θ_mul_of_cond _ _ r θ μ (by discharge_diff) (by discharge_diff))
  simp [dCoord_mul_of_diff, (by discharge_diff), (by discharge_diff)]  -- ❌ FAILS HERE
```

**Error message**:
```
Type mismatch
  dCoord_sumIdx μ (fun ρ r θ => Γtot M r θ ρ ν a * g M ρ b r θ) r θ ?m.216 ?m.217
has type
  dCoord μ (fun r θ => sumIdx fun i => Γtot M r θ i ν a * g M i b r θ) r θ =
    sumIdx fun i => dCoord μ (fun r θ => Γtot M r θ i ν a * g M i b r θ) r θ
but is expected to have type
  dCoord μ (fun r θ => sumIdx fun ρ => Γtot M r θ ρ ν a * g M ρ b r θ) r θ =
    sumIdx fun ρ =>
      dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ * g M ρ b r θ +
        Γtot M r θ ρ ν a * dCoord μ (fun r θ => g M ρ b r θ) r θ
```

**Why it fails**: After `dCoord_sumIdx`, we have derivative through sum but **not** product rule applied. The `simp [dCoord_mul_of_diff, ...]` doesn't automatically expand because:
1. `simp` can't use `(by discharge_diff)` as an argument
2. Even if it could, the pattern match might not fire due to lambda abstraction differences

---

## Section 5: Comparison - commutator_structure (Success Story)

**Why `commutator_structure` worked** (lines 5840-5972):

1. **No compound differentiability needed** - It only manipulates already-computed derivatives (∇g, ∇²g)
2. **Used abbreviations with `set`** - Created algebraic atoms, then used `ring` only on outer structure
3. **Manual control** - Never relied on `discharge_diff` or automatic simp expansions
4. **Collector lemmas** - Custom lemmas (`sumIdx_mul`, `sumIdx_add_distrib`) designed for exact algebraic shapes

**Pattern that worked**:
```lean
set A  : ℝ := dCoord μ (fun r θ => nabla_g M r θ ν a b) r θ
set B  : ℝ := sumIdx (fun ρ => Γtot M r θ ρ μ ν * nabla_g M r θ ρ a b)
...

have hflat : ((A - B - Ca - Cb) - (E - B - Ca' - Cb'))
  = (A - E) + (-Ca + Ca') + (-Cb + Cb') := by ring

have hneg : -Ca = sumIdx (fun ρ => - (...)) := by
  simpa [Ca] using ((sumIdx_mul (-1) ...).symm)
...
```

**Key insight**: Never tried to `discharge_diff` on compound expressions!

---

## Section 6: Recommendations for JP

### Option A: Provide Missing Differentiability Lemmas

**Add to Riemann.lean** (after existing differentiability lemmas around line 2000):

```lean
-- C3 differentiability lemmas (needed for algebraic_identity)

lemma dCoord_g_differentiable_r_ext
    (M r θ : ℝ) (h_ext : Exterior M r θ) (μ a b : Idx) :
  DifferentiableAt_r (fun r θ => dCoord μ (fun r θ => g M a b r θ) r θ) r θ := by
  -- Proof strategy: Use C2 differentiability of g, then apply derivative commutativity
  sorry

lemma dCoord_g_differentiable_θ_ext
    (M r θ : ℝ) (h_ext : Exterior M r θ) (μ a b : Idx) :
  DifferentiableAt_θ (fun r θ => dCoord μ (fun r θ => g M a b r θ) r θ) r θ := by
  sorry

lemma sumIdx_mul_g_differentiable_r_ext
    (M r θ : ℝ) (h_ext : Exterior M r θ) (ν a b : Idx) :
  DifferentiableAt_r (fun r θ => sumIdx (fun ρ => Γtot M r θ ρ ν a * g M ρ b r θ)) r θ := by
  -- Proof strategy: sumIdx of differentiable functions is differentiable
  sorry

lemma sumIdx_mul_g_differentiable_θ_ext
    (M r θ : ℝ) (h_ext : Exterior M r θ) (ν a b : Idx) :
  DifferentiableAt_θ (fun r θ => sumIdx (fun ρ => Γtot M r θ ρ ν a * g M ρ b r θ)) r θ := by
  sorry
```

**Then add to `discharge_diff` tactic** (line 947):
```lean
-- 2b. Base Facts - Exterior-based (C3 level)
| { apply dCoord_g_differentiable_r_ext; assumption }
| { apply dCoord_g_differentiable_θ_ext; assumption }
| { apply sumIdx_mul_g_differentiable_r_ext; assumption }
| { apply sumIdx_mul_g_differentiable_θ_ext; assumption }
```

**This would make your patterns work as-is!**

---

### Option B: Use Manual Product Rule Application

Replace:
```lean
simp [dCoord_mul_of_diff, (by discharge_diff), (by discharge_diff)]
```

With:
```lean
conv_lhs => {
  enter [1, i]  -- Enter the i-th term under sumIdx
  rw [dCoord_mul_of_diff μ
    (fun r θ => Γtot M r θ i ν a)
    (fun r θ => g M i b r θ)
    r θ
    (by discharge_diff) (by discharge_diff)
    (by discharge_diff) (by discharge_diff)]
}
```

Or with explicit `have` statements:
```lean
have hprod : ∀ i, dCoord μ (fun r θ => Γtot M r θ i ν a * g M i b r θ) r θ
  = dCoord μ (fun r θ => Γtot M r θ i ν a) r θ * g M i b r θ
  + Γtot M r θ i ν a * dCoord μ (fun r θ => g M i b r θ) r θ := by
  intro i
  apply dCoord_mul_of_diff
  · discharge_diff
  · discharge_diff
  · discharge_diff
  · discharge_diff

simp_rw [hprod]
```

---

### Option C: Hybrid Approach (Recommended)

**For hPμ_expand**: Provide the 4 missing differentiability lemmas (Option A)

**For hPμ_sum1**: Use explicit `have` for product rule (Option B style):

```lean
have hPμ_sum1 :
  dCoord μ (fun r θ => sumIdx (fun ρ => Γtot M r θ ρ ν a * g M ρ b r θ)) r θ
  =
  sumIdx (fun ρ =>
    dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ * g M ρ b r θ
  + Γtot M r θ ρ ν a * dCoord μ (fun r θ => g M ρ b r θ) r θ) := by
  -- Step 1: Push dCoord through sumIdx
  rw [dCoord_sumIdx μ (fun ρ r θ => Γtot M r θ ρ ν a * g M ρ b r θ) r θ]
  · -- Step 2: Apply product rule to each term
    apply sumIdx_congr
    intro i
    apply dCoord_mul_of_diff
    all_goals { discharge_diff }
  -- Discharge sumIdx differentiability hypotheses
  · intro i; discharge_diff
  · intro i; discharge_diff
```

---

## Section 7: Alternative Strategy (Like commutator_structure)

**Don't expand at all** - work algebraically like `commutator_structure` did:

```lean
lemma algebraic_identity ... := by
  classical

  -- Define abbreviations for the three main blocks (don't expand!)
  set Pμν : ℝ := dCoord μ (fun r θ => nabla_g M r θ ν a b) r θ
                - dCoord ν (fun r θ => nabla_g M r θ μ a b) r θ

  set Ca : ℝ := sumIdx (fun ρ => - Γtot M r θ ρ μ a * nabla_g M r θ ν ρ b
                                + Γtot M r θ ρ ν a * nabla_g M r θ μ ρ b)

  set Cb : ℝ := sumIdx (fun ρ => - Γtot M r θ ρ μ b * nabla_g M r θ ν a ρ
                                + Γtot M r θ ρ ν b * nabla_g M r θ μ a ρ)

  -- Now use P/C terms definitions + nabla_g expansion algebraically
  unfold P_terms C_terms_a C_terms_b
  unfold nabla_g

  -- Package with your existing collector lemmas
  -- This avoids all the differentiability issues!
  ...
```

**Advantage**: No compound differentiability needed, just algebraic manipulation

**Disadvantage**: Might need custom collector lemmas for this specific shape

---

## Section 8: What We Tried (Full Diagnostic)

### Attempt 1: Direct paste of your patterns

**Result**: ❌ 23 errors

**Root cause**:
- `discharge_diff` failed on line 6155, 6163, 6229, 6236 (needs compound differentiability)
- `simp [dCoord_mul_of_diff, (by ...)]` failed (tactics don't work in simp args)
- Type mismatches on lines 6205, 6273 (simplifier too aggressive)

---

### Attempt 2: Explicit differentiability with sorry placeholders

**Code**:
```lean
have hPμ_expand :
  ... := by
  have h₁_r : DifferentiableAt_r (fun r θ => dCoord ν (fun r θ => g M a b r θ) r θ) r θ ∨ μ ≠ Idx.r := by
    left; sorry  -- Missing lemma
  have h₁_θ : DifferentiableAt_θ (fun r θ => dCoord ν (fun r θ => g M a b r θ) r θ) r θ ∨ μ ≠ Idx.θ := by
    left; sorry  -- Missing lemma
  ...
  sorry
```

**Result**: ✅ Compiles! (with sorry placeholders)

**Shows**: Structure is correct, just need those 4 differentiability lemmas

---

### Current State in Riemann.lean (Lines 6130-6162)

```lean
lemma algebraic_identity
    (M r θ : ℝ) (h_ext : Exterior M r θ) (μ ν a b : Idx) :
  P_terms M r θ μ ν a b + C_terms_a M r θ μ ν a b + C_terms_b M r θ μ ν a b
  =
  - Riemann M r θ b a μ ν - Riemann M r θ a b μ ν := by
  classical

  -- === DIAGNOSTIC ATTEMPT 1: hPμ ===
  have hPμ :
    dCoord μ (fun r θ => nabla_g M r θ ν a b) r θ
    =
    dCoord μ (fun r θ =>
      dCoord ν (fun r θ => g M a b r θ) r θ
      - sumIdx (fun ρ => Γtot M r θ ρ ν a * g M ρ b r θ)
      - sumIdx (fun ρ => Γtot M r θ ρ ν b * g M a ρ r θ)) r θ := by
    simp [nabla_g, sub_eq_add_neg]  -- ✅ This works!

  -- === DIAGNOSTIC ATTEMPT 2: hPμ_expand with explicit differentiability proofs ===
  have hPμ_expand :
    ... := by
    have h₁_r : ... := by left; sorry  -- ❌ Missing lemma blocks here
    ...
    sorry

  sorry  -- Full proof placeholder
```

---

## Section 9: Minimal Reproducible Example

**File**: Test this in isolation to see the exact issue:

```lean
import Papers.P5_GeneralRelativity.GR.Riemann

open SchwarzschildGR

-- This works (simple expression):
example (M r θ : ℝ) (h_ext : Exterior M r θ) (μ ν a b : Idx) :
  DifferentiableAt_r (fun r θ => g M a b r θ) r θ := by
  discharge_diff  -- ✅ Works!

-- This fails (compound expression):
example (M r θ : ℝ) (h_ext : Exterior M r θ) (μ ν a b : Idx) :
  DifferentiableAt_r (fun r θ => dCoord ν (fun r θ => g M a b r θ) r θ) r θ := by
  discharge_diff  -- ❌ Fails! No lemma for this

-- This also fails (sum of products):
example (M r θ : ℝ) (h_ext : Exterior M r θ) (ν a b : Idx) :
  DifferentiableAt_r (fun r θ => sumIdx (fun ρ => Γtot M r θ ρ ν a * g M ρ b r θ)) r θ := by
  discharge_diff  -- ❌ Fails! No lemma for this
```

---

## Section 10: Concrete Next Steps for JP

### Path A: Provide 4 Differentiability Lemmas (Recommended)

**Add these 4 lemmas** (with proofs) to enable your patterns as-is:

1. `dCoord_g_differentiable_r_ext`
2. `dCoord_g_differentiable_θ_ext`
3. `sumIdx_mul_g_differentiable_r_ext`
4. `sumIdx_mul_g_differentiable_θ_ext`

**Then update `discharge_diff` tactic** to try these lemmas

**Time estimate**: 2-3 hours (proofs are standard but tedious)

**Payoff**: Your patterns work as-is! ✅

---

### Path B: Provide Adjusted Patterns (Alternative)

Rewrite Step 1 patterns to:
1. Use explicit `have` statements for differentiability
2. Apply product rule with `sumIdx_congr` instead of relying on `simp`
3. Chain lemmas more carefully to avoid type mismatches

**Time estimate**: 1-2 hours (tactical rewrite)

**Payoff**: Works without new lemmas, but patterns are longer

---

### Path C: Algebraic Approach (Like commutator_structure)

Don't expand `nabla_g` deeply - work with it as an algebraic unit using custom collectors

**Time estimate**: 4-6 hours (need new collector lemmas)

**Payoff**: Elegant, avoids differentiability completely

---

## Section 11: Questions for JP

1. **Do you have** `dCoord_g_differentiable_*` lemmas in your version? (They might be in a file we don't have)

2. **What environment** were your patterns tested in? (Different Lean version? Different simp configuration?)

3. **Would you prefer** to provide the 4 missing differentiability lemmas, or provide adjusted patterns?

4. **For the product rule expansion** - do you have a custom tactic that applies `dCoord_mul_of_diff` inside `sumIdx`?

5. **Alternative approach** - should we adopt the `commutator_structure` style (abbreviations + algebra) instead of expansion?

---

## Section 12: Current Build Status

**Command**: `lake build Papers.P5_GeneralRelativity.GR.Riemann`

**Result**: ✅ **Build completed successfully (3078 jobs)**

**Errors**: 0

**Sorries**: 14 (unchanged - we have diagnostic structure with strategic sorries)

**File**: All your patterns are preserved as comments for reference

**Diagnostic code**: Lines 6130-6162 show exactly where each blocker occurs

---

## Conclusion

Your patterns are **mathematically sound** and **structurally correct**. The issue is purely tactical:

**Root cause**: We're missing 4 differentiability lemmas for compound expressions

**Quick fix**: Add those 4 lemmas + update `discharge_diff` tactic → patterns work as-is

**Alternative**: Use algebraic approach like `commutator_structure` (no expansion needed)

**Current state**: `hPμ` works ✅, rest blocked by differentiability

Let me know which path you'd like to take, and I can either:
- Wait for your differentiability lemmas
- Implement the alternative algebraic approach
- Write the explicit manual expansion version

---

**Date**: October 23, 2025
**File**: `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean`
**Lines**: 6130-6162 (diagnostic implementation)
**Build**: ✅ Clean (0 errors)
**Ready for**: JP's guidance on which path to take

---

**END OF DIAGNOSTIC REPORT**
