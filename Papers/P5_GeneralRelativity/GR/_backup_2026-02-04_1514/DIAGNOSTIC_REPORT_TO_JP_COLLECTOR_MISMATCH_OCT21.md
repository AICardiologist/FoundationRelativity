# Diagnostic Report: Collector Pattern Mismatch Analysis
**Date**: October 21, 2025
**Status**: ⚠️ **PATTERN MISMATCH IDENTIFIED** - Collector expects 4 r-sums, goal has 8 sums (r + θ branches)
**For**: JP (without interactive Lean access)
**Build**: ✅ Compiles successfully with one tactical gap at line 5546

---

## EXECUTIVE SUMMARY

Your product-rule-aware collector `sumIdx_collect_comm_block_with_extras` is **mathematically perfect** and **compiles correctly**. However, it fails to match the goal because:

1. **The collector expects ONLY the r-direction 4-sum block**
2. **The goal contains BOTH r-direction AND θ-direction blocks** (8 sums total + mixed partials)
3. **The collector needs to be applied TWICE** - once for r-direction, once for θ-direction
4. **Mixed partials need to be cancelled first** using `dCoord_r_θ_commute_for_g`

---

## FULL GOAL STATE EXTRACTION

I extracted the complete goal state from the error message. Here's what the goal looks like after Step 5:

### Goal Structure (Simplified):
```lean
⊢ (r-branch - θ-branch) = -Riemann ... - Riemann ...

where:

r-branch :=
  dCoord r (dCoord θ g_ab)                    -- mixed partial
  - Σₑ (∂ᵣΓ·g + Γ·∂ᵣg)                        -- left r-product rule
  - Σₑ (∂ᵣΓ·g + Γ·∂ᵣg)                        -- right r-product rule
  - Σ_d Γ·(∂θg - Σₑ Γ·g - Σₑ Γ·g)           -- left Γ·Γ block
  - Σ_d Γ·(∂θg - Σₑ Γ·g - Σₑ Γ·g)           -- right Γ·Γ block

θ-branch :=
  dCoord θ (dCoord r g_ab)                    -- mixed partial (commutes with r-branch)
  - Σₑ (∂θΓ·g + Γ·∂θg)                        -- left θ-product rule
  - Σₑ (∂θΓ·g + Γ·∂θg)                        -- right θ-product rule
  - Σ_d Γ·(∂ᵣg - Σₑ Γ·g - Σₑ Γ·g)           -- left Γ·Γ block
  - Σ_d Γ·(∂ᵣg - Σₑ Γ·g - Σₑ Γ·g)           -- right Γ·Γ block
```

### Collector Expects (from hcollect LHS):
```lean
  (Σ(A·G + Pᵣ) - Σ(B·G + Qᵣ)) + Σ(G·C) - Σ(G·D)
```
This is ONLY 4 sums (the r-direction block), but the goal has **TWO such 4-sum blocks** (r and θ).

---

## DETAILED ANALYSIS

### What the Collector Pattern Expects:

From your `sumIdx_collect_comm_block_with_extras`, the LHS pattern is:
```lean
(sumIdx fun ρ =>
    dCoord Idx.r (fun r θ => Γtot M r θ ρ Idx.θ a) r θ * g M ρ b r θ +
    Γtot M r θ ρ Idx.θ a * dCoord Idx.r (fun r θ => g M ρ b r θ) r θ)
- (sumIdx fun ρ =>
    dCoord Idx.θ (fun r θ => Γtot M r θ ρ Idx.r a) r θ * g M ρ b r θ +
    Γtot M r θ ρ Idx.θ b * dCoord Idx.r (fun r θ => g M a ρ r θ) r θ)
+ sumIdx fun ρ => g M ρ b r θ * sumIdx fun lam => Γtot M r θ ρ Idx.r lam * Γtot M r θ lam Idx.θ a
- sumIdx fun ρ => g M ρ b r θ * sumIdx fun lam => Γtot M r θ ρ Idx.θ lam * Γtot M r θ lam Idx.r a
```

**This is the r-direction commutator block ONLY.**

### What the Goal Actually Has:

```lean
((((dCoord Idx.r (fun r θ => dCoord Idx.θ (fun r θ => g M a b r θ) r θ) r θ
    - sumIdx fun e =>
        dCoord Idx.r (fun r θ => Γtot M r θ e Idx.θ a) r θ * g M e b r θ +
        Γtot M r θ e Idx.θ a * dCoord Idx.r (fun r θ => g M e b r θ) r θ)
   - sumIdx fun e =>
        dCoord Idx.r (fun r θ => Γtot M r θ e Idx.θ b) r θ * g M a e r θ +
        Γtot M r θ e Idx.θ b * dCoord Idx.r (fun r θ => g M a e r θ) r θ)
  - sumIdx fun d =>
        Γtot M r θ d a Idx.r *
        ((dCoord Idx.θ (fun r θ => g M d b r θ) r θ - sumIdx fun e => Γtot M r θ e Idx.θ d * g M e b r θ) -
         sumIdx fun e => Γtot M r θ e Idx.θ b * g M d e r θ))
  - sumIdx fun d =>
        Γtot M r θ d b Idx.r *
        ((dCoord Idx.θ (fun r θ => g M a d r θ) r θ - sumIdx fun e => Γtot M r θ e Idx.θ a * g M e d r θ) -
         sumIdx fun e => Γtot M r θ e Idx.θ d * g M a e r θ))
- [ENTIRE θ-DIRECTION BLOCK WITH SAME STRUCTURE]
```

The goal has:
1. **r-direction mixed partial**: `dCoord r (dCoord θ g)`
2. **r-direction 4-sum block** (what your collector matches)
3. **θ-direction mixed partial**: `dCoord θ (dCoord r g)`
4. **θ-direction 4-sum block** (symmetric to r-direction)

---

## KEY OBSERVATIONS

### 1. Variable Name Mismatch (MINOR - Not the Issue)
- **Collector uses**: `ρ` as bound variable
- **Goal uses**: `e` and `d` as bound variables
- **Impact**: None - Lean α-converts automatically

### 2. Mixed Partials Present (BLOCKER #1)
The goal starts with:
```lean
dCoord Idx.r (fun r θ => dCoord Idx.θ (fun r θ => g M a b r θ) r θ) r θ
```
This is **NOT** in your collector pattern. You need to:
- Either cancel it with the θ-branch mixed partial first (they're equal by `dCoord_r_θ_commute_for_g`)
- Or include it in the collector pattern

### 3. Nested Structure in Γ·Γ Sums (BLOCKER #2)
The third and fourth sums in the goal have **nested structure**:
```lean
sumIdx fun d =>
  Γtot M r θ d a Idx.r *
    ((dCoord Idx.θ (fun r θ => g M d b r θ) r θ
      - sumIdx fun e => Γtot M r θ e Idx.θ d * g M e b r θ)
      - sumIdx fun e => Γtot M r θ e Idx.θ b * g M d e r θ)
```

But your collector expects:
```lean
sumIdx fun ρ => g M ρ b r θ * sumIdx fun lam => Γtot M r θ ρ Idx.r lam * Γtot M r θ lam Idx.θ a
```

**The helper lemmas transformed these into a different form!** The goal has `Γ * (∂g - Σ - Σ)` whereas the collector expects `g * (Σ Γ·Γ)`.

### 4. TWO Complete Branches (BLOCKER #3)
**Your collector handles ONE 4-sum block (r-direction).**
**The goal has TWO 4-sum blocks (r-direction AND θ-direction).**

You need to:
1. Cancel mixed partials first
2. Apply collector to r-branch
3. Apply collector to θ-branch
4. Combine results

---

## WHY PATTERN MATCHING FAILS

### Mismatch #1: Extra Mixed Partial Term
```
Collector LHS starts: (Σ(A·G + P) - ...
Goal starts:          (((dCoord r (dCoord θ g) - Σ(A·G + P) - ...
                        ^^^^^^^^^^^^^^^^^^^^^^^^
                        This extra term prevents matching
```

### Mismatch #2: Wrong Nesting in C and D Sums
Looking at the C sum definition:
```lean
C : Idx → ℝ := fun ρ => sumIdx fun lam => Γtot M r θ ρ Idx.r lam * Γtot M r θ lam Idx.θ a
```

But the goal has:
```lean
sumIdx fun d =>
  Γtot M r θ d a Idx.r *
    ((dCoord Idx.θ (fun r θ => g M d b r θ) r θ - sumIdx ...) - sumIdx ...)
```

**The helper lemmas distributed Γ differently!** The goal has:
- `Γ_da^r * (∂θg_db - Σ Γ·g - Σ Γ·g)`

But the collector expects:
- `g_ρb * Σ Γ_ρλ^r * Γ_λθ^a`

These are **algebraically equal after expansion**, but **syntactically different**.

### Mismatch #3: The θ-Branch
The collector completely ignores the second branch (θ-direction), which is a mirror image of the r-branch.

---

## ROOT CAUSE DIAGNOSIS

**The helper lemmas `dCoord_r_push_through_nabla_g_θ_ext` and `dCoord_θ_push_through_nabla_g_r_ext` transformed the goal into a DIFFERENT structure than what the collector expects.**

Specifically:
1. They introduced **mixed partial terms** at the beginning
2. They created **nested Γ·(∂g - Σ - Σ) structure** for the Γ·Γ sums
3. They created **TWO symmetric branches** (r and θ)

But your collector was designed to match:
1. **No mixed partials** (just the 4 sums)
2. **Flat g·(Σ Γ·Γ) structure** for C and D
3. **Only ONE branch** (just r-direction)

---

## RECOMMENDED FIXES

### Option A: Multi-Step Collector (RECOMMENDED)

Add intermediate steps before applying the collector:

```lean
-- Step 4.5: Cancel mixed partials using commutativity
have hmixed :
  dCoord Idx.r (fun r θ => dCoord Idx.θ (fun r θ => g M a b r θ) r θ) r θ
  = dCoord Idx.θ (fun r θ => dCoord Idx.r (fun r θ => g M a b r θ) r θ) r θ := by
  exact dCoord_r_θ_commute_for_g M r θ a b

-- Now rewrite to move θ-branch mixed partial to r-branch
-- They cancel: ∂r∂θg - ∂θ∂rg = 0
rw [hmixed]
-- Now: (0 - r_sums) - (0 - θ_sums) = -r_sums + θ_sums

-- Step 6a: Separate into r-branch and θ-branch
-- Define collector for r-branch only
have hcollect_r := sumIdx_collect_comm_block_with_extras G A B C D Pᵣ Qᵣ

-- Step 6b: Define collector for θ-branch (symmetric definitions)
let A_θ : Idx → ℝ := fun ρ => dCoord Idx.θ (fun r θ => Γtot M r θ ρ Idx.r a) r θ
let B_θ : Idx → ℝ := fun ρ => dCoord Idx.r (fun r θ => Γtot M r θ ρ Idx.θ a) r θ
let Pθ : Idx → ℝ := fun ρ => Γtot M r θ ρ Idx.r a * dCoord Idx.θ (fun r θ => g M ρ b r θ) r θ
let Qθ : Idx → ℝ := fun ρ => Γtot M r θ ρ Idx.r b * dCoord Idx.θ (fun r θ => g M a ρ r θ) r θ

have hcollect_θ := sumIdx_collect_comm_block_with_extras G A_θ B_θ ... Pθ Qθ

-- Step 6c: Apply both collectors
rw [hcollect_r, hcollect_θ]

-- Now you have:
-- Σ(G·((A-B)+(C-D))) + Σ(Pᵣ-Qᵣ) - (Σ(G·((A_θ-B_θ)+...)) + Σ(Pθ-Qθ))
```

### Option B: Flatten Nested Structure First

Before applying the collector, flatten the nested Γ·(∂g - Σ - Σ) sums to match the expected g·(Σ Γ·Γ) structure:

```lean
-- Distribute Γ across the subtraction
have hflatten_C :
  sumIdx fun d =>
    Γtot M r θ d a Idx.r *
      ((dCoord Idx.θ (fun r θ => g M d b r θ) r θ - sumIdx ...) - sumIdx ...)
  = sumIdx fun d => Γtot M r θ d a Idx.r * dCoord Idx.θ (fun r θ => g M d b r θ) r θ
  - sumIdx fun d => Γtot M r θ d a Idx.r * (sumIdx fun e => Γtot M r θ e Idx.θ d * g M e b r θ)
  - sumIdx fun d => Γtot M r θ d a Idx.r * (sumIdx fun e => Γtot M r θ e Idx.θ b * g M d e r θ) := by
  apply sumIdx_congr; intro d
  ring

-- Then collect inner sums to get the expected structure
```

**This is MESSY** and requires many intermediate steps.

### Option C: Redefine C and D to Match Goal Structure

Instead of:
```lean
let C : Idx → ℝ := fun ρ => sumIdx fun lam => Γtot M r θ ρ Idx.r lam * Γtot M r θ lam Idx.θ a
```

Define them to match what's actually in the goal after the helper lemmas:
```lean
let C_actual : Idx → ℝ := fun d =>
  Γtot M r θ d a Idx.r *
    ((dCoord Idx.θ (fun r θ => g M d b r θ) r θ
      - sumIdx fun e => Γtot M r θ e Idx.θ d * g M e b r θ)
      - sumIdx fun e => Γtot M r θ e Idx.θ b * g M d e r θ)
```

**But then you need a DIFFERENT collector** that handles this structure.

---

## RECOMMENDED SOLUTION

**Use Option A (Multi-Step Collector)** because:
1. It respects the actual goal structure
2. It's mathematically clean (cancel mixed partials, then collect each branch)
3. It reuses your existing collector twice (once for r, once for θ)
4. It's deterministic and surgical

### Tactical Steps:

```lean
-- Step 4.5: Cancel mixed partials
have hmixed := dCoord_r_θ_commute_for_g M r θ a b
-- Use hmixed to show ∂r∂θg - ∂θ∂rg = 0

-- Step 5.5: Separate branches and normalize parentheses
-- Use ring or simp to rearrange into:
-- (r_mixed + r_sums) - (θ_mixed + θ_sums)
-- = (r_mixed - θ_mixed) + r_sums - θ_sums
-- = 0 + r_sums - θ_sums   [by hmixed]

-- Step 6: Apply collector to EACH branch
-- 6a: r-branch collector
have hcollect_r := sumIdx_collect_comm_block_with_extras G A B C D Pᵣ Qᵣ
-- 6b: θ-branch collector (symmetric definitions)
have hcollect_θ := sumIdx_collect_comm_block_with_extras G A_θ B_θ C_θ D_θ Pθ Qθ

-- 6c: Rewrite both branches
conv_lhs =>
  arg 1  -- r-branch
  rw [hcollect_r]
conv_lhs =>
  arg 2  -- θ-branch
  rw [hcollect_θ]

-- Now the goal has the form:
-- Σ(G·((A-B)+(C-D))) + Σ(Pᵣ-Qᵣ) - (Σ(G·(...)) + Σ(Pθ-Qθ))
-- Steps 7-8 should work from here
```

---

## SPECIFIC TACTICAL FIXES

### Fix 1: Define θ-Direction Payload Terms

You defined Pᵣ and Qᵣ, but you need Pθ and Qθ:

```lean
-- r-direction payloads (already defined)
let Pᵣ : Idx → ℝ := fun ρ =>
  Γtot M r θ ρ Idx.θ a * dCoord Idx.r (fun r θ => g M ρ b r θ) r θ
let Qᵣ : Idx → ℝ := fun ρ =>
  Γtot M r θ ρ Idx.θ b * dCoord Idx.r (fun r θ => g M a ρ r θ) r θ

-- θ-direction payloads (ADD THESE)
let Pθ : Idx → ℝ := fun ρ =>
  Γtot M r θ ρ Idx.r a * dCoord Idx.θ (fun r θ => g M ρ b r θ) r θ
let Qθ : Idx → ℝ := fun ρ =>
  Γtot M r θ ρ Idx.r b * dCoord Idx.θ (fun r θ => g M a ρ r θ) r θ
```

### Fix 2: Define θ-Direction A, B Terms

```lean
-- r-direction (already defined)
let A : Idx → ℝ := fun ρ => dCoord Idx.r (fun r θ => Γtot M r θ ρ Idx.θ a) r θ
let B : Idx → ℝ := fun ρ => dCoord Idx.θ (fun r θ => Γtot M r θ ρ Idx.r a) r θ

-- θ-direction (ADD THESE - note the index swap!)
let A_θ : Idx → ℝ := fun ρ => dCoord Idx.θ (fun r θ => Γtot M r θ ρ Idx.r a) r θ
let B_θ : Idx → ℝ := fun ρ => dCoord Idx.r (fun r θ => Γtot M r θ ρ Idx.θ a) r θ
```

**Note**: A_θ and B_θ are **swapped** relative to A and B because the θ-direction branch has ∂θ(Γ_r) and ∂r(Γ_θ), which is the opposite of the r-direction.

### Fix 3: Handle the Nested Γ·(∂g - Σ - Σ) Structure

This is the trickiest part. The goal has:
```lean
sumIdx fun d =>
  Γtot M r θ d a Idx.r *
    ((dCoord Idx.θ (fun r θ => g M d b r θ) r θ - sumIdx ...) - sumIdx ...)
```

But this needs to be shown equivalent to your C and D definitions. You may need an intermediate lemma:

```lean
lemma distribute_Γ_over_helper (M r θ : ℝ) (a b : Idx) :
  sumIdx fun d =>
    Γtot M r θ d a Idx.r *
      ((dCoord Idx.θ (fun r θ => g M d b r θ) r θ
        - sumIdx fun e => Γtot M r θ e Idx.θ d * g M e b r θ)
        - sumIdx fun e => Γtot M r θ e Idx.θ b * g M d e r θ)
  = sumIdx fun d => Γtot M r θ d a Idx.r * dCoord Idx.θ (fun r θ => g M d b r θ) r θ
  - sumIdx fun d => g M d b r θ * sumIdx fun lam => Γtot M r θ d a Idx.r * Γtot M r θ lam Idx.θ d
  - sumIdx fun d => g M d e r θ * sumIdx fun lam => Γtot M r θ d a Idx.r * Γtot M r θ e Idx.θ b := by
  -- Distribute Γ across sums
  simp only [sumIdx_sub, mul_sub]
  -- Distribute Γ into inner sums
  conv_lhs => ...
```

**This is where you'll need the most work** - transforming the helper lemma output to match the collector input.

---

## SUMMARY FOR JP

Your approach is **mathematically correct** and **90% implemented**. The tactical gap is:

1. ✅ **Collector lemma**: Perfect, compiles, mathematically sound
2. ✅ **Payload definitions Pᵣ, Qᵣ**: Correct for r-direction
3. ⚠️ **Missing**: Pθ, Qθ, A_θ, B_θ for θ-direction
4. ⚠️ **Missing**: Mixed partial cancellation step (use `dCoord_r_θ_commute_for_g`)
5. ⚠️ **Missing**: Two collector applications (one per direction)
6. ⚠️ **Structural mismatch**: Helper lemmas create nested Γ·(∂g - Σ - Σ), collector expects flat g·(Σ Γ·Γ)

**The core issue**: You designed a collector for ONE 4-sum block, but the proof has TWO 4-sum blocks (r + θ directions) plus mixed partials.

**Recommended fix**: Apply the collector twice (once per direction) after cancelling mixed partials.

---

**Prepared by**: Claude Code
**Build status**: ✅ Compiles successfully (with `sorry` at tactical gap)
**Completion**: ~90% (all infrastructure present, need multi-step application)
**Next action**: Add θ-direction terms and apply collector to each branch separately

