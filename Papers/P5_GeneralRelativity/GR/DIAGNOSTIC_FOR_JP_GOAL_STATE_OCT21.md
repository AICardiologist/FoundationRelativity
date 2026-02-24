# Diagnostic Report for JP: Goal State Analysis
**Date**: October 21, 2025
**Status**: **ROOT CAUSE IDENTIFIED** - Product rule creates structure incompatible with flat collector
**For**: JP (without interactive Lean access)

---

## EXECUTIVE SUMMARY

Your fix (`attribute [local irreducible] g` + `simp_rw`) is theoretically perfect and correctly implemented. However, I've extracted the **full goal state** from the error message and identified the root cause:

**The product rule lemmas create a structure that the flat collector cannot match.**

Specifically:
- **Collector expects**: `sumIdx (fun ρ => A ρ * g M ρ b r θ)` — single term per sum
- **Goal actually has**: `sumIdx (fun e => dΓ·g + Γ·dg)` — **two** additive terms per sum (from product rule)

The four-sum block is NOT present in the goal in ANY form that matches the collector pattern.

---

## FULL GOAL STATE (Extracted from Error Message)

### What the Collector Pattern Expects:

```lean
(((sumIdx fun ρ => dCoord Idx.r (fun r θ => Γtot M r θ ρ Idx.θ a) r θ * g M ρ b r θ) -
     sumIdx fun ρ => dCoord Idx.θ (fun r θ => Γtot M r θ ρ Idx.r a) r θ * g M ρ b r θ) +
   sumIdx fun ρ => g M ρ b r θ * sumIdx fun lam => Γtot M r θ ρ Idx.r lam * Γtot M r θ lam Idx.θ a) -
 sumIdx fun ρ => g M ρ b r θ * sumIdx fun lam => Γtot M r θ ρ Idx.θ lam * Γtot M r θ lam Idx.r a
```

### What the Goal Actually Has (After Step 5):

```lean
((((dCoord Idx.r (fun r θ => dCoord Idx.θ (fun r θ => g M a b r θ) r θ) r θ -
          sumIdx fun e =>
            dCoord Idx.r (fun r θ => Γtot M r θ e Idx.θ a) r θ * g M e b r θ +
            Γtot M r θ e Idx.θ a * dCoord Idx.r (fun r θ => g M e b r θ) r θ) -
        sumIdx fun e =>
          dCoord Idx.r (fun r θ => Γtot M r θ e Idx.θ b) r θ * g M a e r θ +
          Γtot M r θ e Idx.θ b * dCoord Idx.r (fun r θ => g M a e r θ) r θ) -
      sumIdx fun d =>
        Γtot M r θ d a Idx.r *
          ((dCoord Idx.θ (fun r θ => g M d b r θ) r θ - sumIdx fun e => Γtot M r θ e Idx.θ d * g M e b r θ) -
            sumIdx fun e => Γtot M r θ e Idx.θ b * g M d e r θ)) -
    sumIdx fun d =>
      Γtot M r θ d b Idx.r *
        ((dCoord Idx.θ (fun r θ => g M a d r θ) r θ - sumIdx fun e => Γtot M r θ e Idx.θ a * g M e d r θ) -
          sumIdx fun e => Γtot M r θ e Idx.θ d * g M a e r θ))
  - [symmetric θ branch]
```

---

## KEY OBSERVATIONS

### 1. Product Rule Created Two-Term Sums

The product rule lemma `dCoord_r_sumIdx_Γθ_g_left_ext` (line 3861-3867) produces:

```lean
dCoord Idx.r (fun r θ => sumIdx (fun e => Γtot ... * g M e b r θ)) r θ
  =
sumIdx (fun e =>
  dCoord Idx.r (fun r θ => Γtot M r θ e Idx.θ a) r θ * g M e b r θ
+ Γtot M r θ e Idx.θ a * dCoord Idx.r (fun r θ => g M e b r θ) r θ)
```

**Note the `+` inside the sumIdx**: This is the product rule d(f·g) = df·g + f·dg.

So after Step 5, each of the four expected sums is actually **TWO sums with different structures**:
1. `sumIdx (fun e => dΓ * g)` — derivative of Γ times g
2. `sumIdx (fun e => Γ * dg)` — Γ times derivative of g

### 2. g is NOT Expanded (irreducible works!)

Good news: `g M e b r θ` appears in **folded form** throughout the goal! The `attribute [local irreducible] g` is working perfectly — g has NOT been reduced to a match statement.

The issue is NOT delta-reduction.

### 3. Mixed Partials Still Present

The goal still contains:
```lean
dCoord Idx.r (fun r θ => dCoord Idx.θ (fun r θ => g M a b r θ) r θ) r θ
```

These haven't been cancelled yet. This is expected if we skipped Step 4, but it adds complexity.

### 4. Structural Mismatch

**Collector expects**:
- Four sumIdx terms: `Σ(A*g)`, `Σ(B*g)`, `Σ(g*C)`, `Σ(g*D)`
- Each is a single sumIdx with a single multiplicative term inside

**Goal actually has**:
- Eight sumIdx terms (two per expected sum, from product rule splitting)
- Each has EITHER `dΓ*g` OR `Γ*dg` (not the combined form)
- Plus additional complexity from helper lemma structure

### 5. Variable Name Mismatch

- **Collector uses**: `ρ` as bound variable
- **Goal uses**: `e` and `d` as bound variables

(This is minor and wouldn't prevent matching, but worth noting)

---

## WHY THE COLLECTOR CAN'T MATCH

The flat collector pattern is:

```lean
(sumIdx (fun ρ => A ρ * g M ρ b r θ)) -
(sumIdx (fun ρ => B ρ * g M ρ b r θ)) +
(sumIdx (fun ρ => g M ρ * C ρ)) -
(sumIdx (fun ρ => g M ρ * D ρ))
```

But the goal has things like:

```lean
sumIdx fun e =>
  dCoord Idx.r (fun r θ => Γtot M r θ e Idx.θ a) r θ * g M e b r θ +
  Γtot M r θ e Idx.θ a * dCoord Idx.r (fun r θ => g M e b r θ) r θ
```

The pattern `A ρ * g M ρ b r θ` would need to match `dCoord ... * g M e b r θ + Γtot ... * dCoord ...`, which it cannot because:

1. The sumIdx contains a `+` (two terms), not a single term
2. The second additive term has `dCoord (fun r θ => g M e b r θ)` not `g M e b r θ`
3. The structure is fundamentally different

---

## THE ROOT CAUSE

**The helper lemmas and product rules were designed to distribute derivatives correctly, but they create an intermediate structure that your flat collector cannot recognize.**

Specifically, the product rule splits each `∂(Γ·g)` into **two separate additive parts**:
- Part 1: `∂Γ · g`
- Part 2: `Γ · ∂g`

Your collector expects to see a single sumIdx with `A ρ * g M ρ b r θ` inside, but the goal has a sumIdx with `TERM1 + TERM2` inside, where only TERM1 has the pattern `... * g M e b r θ` and TERM2 has `... * ∂g`.

---

## WHY YOUR FIX DIDN'T WORK

### Your Folding Equalities (hAG, hBG, hGC, hGD)

You defined:
```lean
have hAG :
  sumIdx (fun ρ => A ρ * g M ρ b r θ)
    = sumIdx (fun ρ => A ρ * G ρ) := by ...
```

Where `A ρ = dCoord Idx.r (fun r θ => Γtot M r θ ρ Idx.θ a) r θ`.

This says: "sumIdx of (dΓ times g) equals sumIdx of (dΓ times G)".

But the goal doesn't have `sumIdx (fun ρ => A ρ * g M ρ b r θ)` — it has:
```lean
sumIdx fun e =>
  A e * g M e b r θ + Γtot ... * dCoord (fun r θ => g M e b r θ) r θ
```

So `simp_rw [hAG]` finds no match because the left-hand side of hAG doesn't appear in the goal.

### The Collector Pattern

Similarly, `hcollect_expanded` expects to match:
```lean
sumIdx (fun ρ => A ρ * g M ρ b r θ)
```

But that pattern doesn't exist in the goal due to the product rule split.

---

## WHAT NEEDS TO HAPPEN

To make the collector work, you need to **collect the product-rule terms first**.

### Option A: Collect Each Pair of Product Terms

Before applying the four-sum collector, collect each pair:

```lean
-- For the first pair (from dCoord_r applied to Γθ·g):
have h1 :
  sumIdx fun e =>
    dCoord Idx.r (fun r θ => Γtot M r θ e Idx.θ a) r θ * g M e b r θ +
    Γtot M r θ e Idx.θ a * dCoord Idx.r (fun r θ => g M e b r θ) r θ
  =
  sumIdx fun e =>
    dCoord Idx.r (fun r θ => Γtot M r θ e Idx.θ a * g M e b r θ) r θ := by
  -- This reverses the product rule
  apply sumIdx_congr; intro e
  rw [dCoord_mul_of_diff Idx.r ...]
```

Repeat for all eight product-rule expansions.

This would "fold back" the product rule, giving you sumIdx terms of the form:
```lean
sumIdx (fun e => dCoord Idx.r (fun r θ => Γtot ... * g ...) r θ)
```

Then your collector might match.

### Option B: Different Collector

Write a collector that matches the expanded product-rule form:

```lean
lemma sumIdx_collect_product_rule_form (G A B C D : Idx → ℝ)
    (dG : Idx → ℝ) -- derivative of G
    ... :
  (sumIdx (fun ρ => A ρ * G ρ + A' ρ * dG ρ)) -
  (sumIdx (fun ρ => B ρ * G ρ + B' ρ * dG ρ)) +
  ...
  =
  sumIdx (fun ρ => G ρ * (...)) + sumIdx (fun ρ => dG ρ * (...))
```

This would match the actual structure in the goal.

### Option C: Intermediate Normalization

Add a step between Step 5 and Step 6 that normalizes the product-rule terms:

```lean
-- After Step 5, distribute addition over sumIdx (reverse)
have hcollect_products :
  sumIdx (fun e => TERM1 + TERM2)
    = sumIdx (fun e => TERM1) + sumIdx (fun e => TERM2) := by
  rw [← sumIdx_add]

-- Now you have separate sumIdx terms that can be collected differently
```

Then collect the `dΓ·g` terms separately from the `Γ·dg` terms.

---

## VARIABLES IN SCOPE (From Error Message)

```lean
M r θ : ℝ
h_ext : Exterior M r θ
h_θ : sin θ ≠ 0
a b : Idx
G : Idx → ℝ := fun ρ => g M ρ b r θ
A : Idx → ℝ := fun ρ => dCoord Idx.r (fun r θ => Γtot M r θ ρ Idx.θ a) r θ
B : Idx → ℝ := fun ρ => dCoord Idx.θ (fun r θ => Γtot M r θ ρ Idx.r a) r θ
C : Idx → ℝ := fun ρ => sumIdx fun lam => Γtot M r θ ρ Idx.r lam * Γtot M r θ lam Idx.θ a
D : Idx → ℝ := fun ρ => sumIdx fun lam => Γtot M r θ ρ Idx.θ lam * Γtot M r θ lam Idx.r a
hAG : (sumIdx fun ρ => A ρ * g M ρ b r θ) = sumIdx fun ρ => A ρ * G ρ
hBG : (sumIdx fun ρ => B ρ * g M ρ b r θ) = sumIdx fun ρ => B ρ * G ρ
hGC : (sumIdx fun ρ => g M ρ b r θ * C ρ) = sumIdx fun ρ => G ρ * C ρ
hGD : (sumIdx fun ρ => g M ρ b r θ * D ρ) = sumIdx fun ρ => G ρ * D ρ
```

---

## RECOMMENDED FIX

### Short-Term: Fold Product Rules Back

The cleanest approach is to **reverse the product rule** before applying the collector.

After Step 5, add:

```lean
-- Step 5.5: Fold product-rule expansions back to single derivatives
-- For each of the 4 pairs (left/right, r/θ directions), reverse the product rule

have hfold₁ :
  sumIdx fun e =>
    dCoord Idx.r (fun r θ => Γtot M r θ e Idx.θ a) r θ * g M e b r θ +
    Γtot M r θ e Idx.θ a * dCoord Idx.r (fun r θ => g M e b r θ) r θ
  =
  sumIdx fun e =>
    dCoord Idx.r (fun r θ => Γtot M r θ e Idx.θ a * g M e b r θ) r θ := by
  apply sumIdx_congr
  intro e
  rw [← dCoord_mul_of_diff Idx.r
        (fun r θ => Γtot M r θ e Idx.θ a)
        (fun r θ => g M e b r θ) r θ]
  · simp  -- differentiability for Γ
  · simp  -- differentiability for g
  · simp  -- θ direction (irrelevant)
  · simp  -- θ direction (irrelevant)

-- Repeat for the other 7 product-rule pairs

rw [hfold₁, hfold₂, hfold₃, hfold₄, hfold₅, hfold₆, hfold₇, hfold₈]

-- NOW the goal should have the structure your collector expects
```

### Long-Term: Different Product Rule Lemmas

The product rule lemmas `dCoord_r_sumIdx_Γθ_g_left_ext` could be written to produce the **unexpanded form**:

```lean
lemma dCoord_r_sumIdx_Γθ_g_left_ext_folded
    (M r θ : ℝ) (h_ext : Exterior M r θ) (a b : Idx) :
  dCoord Idx.r (fun r θ => sumIdx (fun e => Γtot M r θ e Idx.θ a * g M e b r θ)) r θ
    =
  sumIdx (fun e =>
    dCoord Idx.r (fun r θ => Γtot M r θ e Idx.θ a * g M e b r θ) r θ) := by
  -- Just push derivative through sum, don't expand the product
  apply dCoord_sumIdx
  ...
```

Then your collector would match directly without needing the folding step.

---

## SUMMARY FOR JP

Your surgical fix is **perfect** and has **no bugs**. The issue is:

1. ✅ `attribute [local irreducible] g` **works** — g is NOT expanded in the goal
2. ✅ Your folding equalities (hAG, etc.) **are correct**
3. ✅ Your collector lemma **is correct**

The problem is:

❌ **The product rule lemmas create a structure that your collector pattern cannot match.**

The product rule splits each `∂(Γ·g)` into `(∂Γ)·g + Γ·(∂g)`, creating **two additive terms inside each sumIdx**. Your collector expects **one multiplicative term inside each sumIdx**.

**Solution**: Add a step after Step 5 that folds the product-rule pairs back together using the reverse of `dCoord_mul_of_diff`, or write new product-rule lemmas that don't expand the products.

---

**Prepared by**: Claude Code
**For**: JP (without interactive Lean access)
**Goal state**: Fully extracted from build error
**Root cause**: Product rule structure mismatch
**Fix**: Reverse product rule before applying collector
