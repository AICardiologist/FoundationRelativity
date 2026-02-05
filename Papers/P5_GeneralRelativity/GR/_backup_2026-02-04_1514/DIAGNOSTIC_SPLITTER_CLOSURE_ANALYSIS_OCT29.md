# Diagnostic Report: Splitter Closure Analysis

**Date**: October 29, 2025
**Status**: ⚠️ **COMPLEX MATHEMATICAL ISSUE IDENTIFIED**
**Error Count**: 23 errors (baseline maintained with JP's lemmas)

---

## Executive Summary

JP's ΓΓ splitter lemmas (`ΓΓ_splitter_b` and `ΓΓ_splitter_a`) have been successfully added to the codebase at lines 7247-7278. They compile cleanly and introduce **no new errors**. However, the two primary unsolved splitter goals at lines **7303** and **7605** reveal a **fundamental mathematical issue** that requires expert resolution.

### Critical Finding

Both splitter goals reduce to proving:
```
g * (A - B) + C = g * (B - A) + C
```
Where `C` is identical on both sides. This simplifies to proving:
```
g * (A - B) = g * (B - A)
```
Which requires either:
1. **A = B** (the two sums are equal), OR
2. **g = 0** (the metric component is zero)

Neither appears to be provable with current infrastructure.

---

## Detailed Analysis

### 1. Line 7303: μ-splitter (b-branch)

**Location**: Inside `ΓΓ_quartet_split_b` proof
**Context**: After establishing multiple helper hypotheses

**Goal State**:
```lean
⊢ (g M b b r θ *
        ((sumIdx fun e => Γtot M r θ b ν e * Γtot M r θ e μ a)
       - (sumIdx fun e => Γtot M r θ b μ e * Γtot M r θ e ν a)) +
      sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ a * Γtot M r θ ρ ν b
                                   - Γtot M r θ ρ ν a * Γtot M r θ ρ μ b)) =
    g M b b r θ *
        ((sumIdx fun e => Γtot M r θ b μ e * Γtot M r θ e ν a)
       - (sumIdx fun e => Γtot M r θ b ν e * Γtot M r θ e μ a)) +
      sumIdx fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ a * Γtot M r θ ρ ν b
                                   - Γtot M r θ ρ ν a * Γtot M r θ ρ μ b)
```

**Simplification**:
- Second `sumIdx` term is identical on both sides → cancels out
- Reduces to proving: `g M b b r θ * (A - B) = g M b b r θ * (B - A)`
- Where:
  - A = `sumIdx fun e => Γtot M r θ b ν e * Γtot M r θ e μ a`
  - B = `sumIdx fun e => Γtot M r θ b μ e * Γtot M r θ e ν a`

**Mathematical Requirement**:
```
A - B = B - A  ⟺  2*(A - B) = 0  ⟺  A = B
```

### 2. Line 7605: ν-splitter (a-branch)

**Location**: Inside `ΓΓ_quartet_split_a` proof
**Context**: Mirror of b-branch with a/b swapped

**Goal State**: Symmetric structure with `g M a a r θ` and indices swapped

**Same Mathematical Issue**: Requires proving two sums are equal.

---

## Available Hypotheses

Both proofs have established these helper facts:

1. **first_block**: Nested sum equality after metric folding
2. **first_block_packed**: Packed form with g factored outside
3. **swap₁, swap₂**: Commutativity of products in sums
4. **first_block_aligned**: Aligned form after swaps
5. **second_block**: Second block equality with diagonal metrics
6. **bb_core_reindexed** (or **aa_core_reindexed**): Reindexing identity

The `bb_core_reindexed` hypothesis states:
```lean
((sumIdx fun ρ => Γtot M r θ ρ μ a * Γtot M r θ b ν ρ)
 - (sumIdx fun ρ => Γtot M r θ ρ ν a * Γtot M r θ b μ ρ)) =
    (sumIdx fun e => Γtot M r θ b ν e * Γtot M r θ e μ a)
  - (sumIdx fun e => Γtot M r θ b μ e * Γtot M r θ e ν a)
```

This establishes that the LHS difference equals a reindexed version. But the **goal requires the difference to equal its negative**.

---

## JP's Splitter Lemmas: Purpose and Limitations

### What They Do

JP's lemmas provide the mechanical split `Σ(A − B) = ΣA − ΣB`:

```lean
lemma ΓΓ_splitter_b (M r θ : ℝ) (ρ μ ν σ : Idx) :
  sumIdx (fun lam => Γtot... ρ μ lam * Γtot... lam,νσ
                   - Γtot... ρ ν lam * Γtot... lam,μσ)
  = (sumIdx (fun lam => Γtot... ρ μ lam * Γtot... lam,νσ))
  - (sumIdx (fun lam => Γtot... ρ ν lam * Γtot... lam,μσ))
```

### What They Don't Do

These lemmas **do not prove** that:
```
Σ(A - B) = -(Σ(A - B))  [which would require A = B]
```

They simply rearrange the structure of sums. The equality A = B would need to come from **symmetry properties of Γtot** that are not currently available or applied.

---

## Root Cause Analysis

### Missing Infrastructure

The proof requires one of these lemmas (none currently exist):

**Option 1**: Christoffel symmetry in contracted products
```lean
lemma Γtot_contracted_symmetry :
  sumIdx (fun e => Γtot M r θ b ν e * Γtot M r θ e μ a) =
  sumIdx (fun e => Γtot M r θ b μ e * Γtot M r θ e ν a)
```

**Option 2**: Antisymmetry of the quartet difference
```lean
lemma ΓΓ_quartet_antisymmetry :
  sumIdx (fun e => Γtot M r θ b ν e * Γtot M r θ e μ a
                 - Γtot M r θ b μ e * Γtot M r θ e ν a) = 0
```

**Option 3**: Index permutation symmetry
```lean
lemma Γtot_permutation_symmetry (M r θ : ℝ) (μ ν a b : Idx) :
  sumIdx (fun e => Γtot M r θ b ν e * Γtot M r θ e μ a) =
  sumIdx (fun e => Γtot M r θ b μ e * Γtot M r θ e ν a)
```

### Mathematical Question

**Is this a valid identity in Schwarzschild geometry?**

The Christoffel symbols have specific symmetry properties:
- Γ^i_{jk} = Γ^i_{kj} (symmetric in lower indices)

But the contracted product `Σ_e Γ^b_{νe} Γ^e_{μa}` involves:
- Different first indices (b vs e)
- Different index patterns

**Question for Senior Professor**: Does the Riemann curvature tensor calculation require a symmetry lemma that makes these contracted products equal? Or is there an error in how the goal was set up?

---

## Paul's Guidance Re-Interpretation

Paul requested the goal states "to provide the exact pointwise H and the precise rw/calc chain." His analysis noted:

> "Both goals have the structure: g * (A - B) + C = g * (B - A) + C"
> "This only holds if A = B or g = 0"
> "Question for Paul: Is there a symmetry property of Γtot that makes these sums equal?"

Paul correctly identified that this requires a **symmetry property**. JP's splitter lemmas were provided as **infrastructure** for manipulating sums, not as a direct solution to these specific goals.

---

## Recommended Actions

### Immediate: Consult Senior Professor (SP)

**Question to SP**:
```
In the Schwarzschild metric Riemann tensor calculation, we encounter:

LHS = Σ_e (Γ^b_{νe} · Γ^e_{μa})
RHS = Σ_e (Γ^b_{μe} · Γ^e_{νa})

Context: μ, ν, a, b are free indices; e is summed over.

Does Schwarzschild geometry provide a symmetry that makes LHS = RHS?

If not, is there an error in how the Riemann tensor quartet was decomposed?
```

### Alternative: Check Git History

These goals may have been **intentionally left as sorry** in earlier versions, indicating they were known blockers. Check if:
1. Original implementation had `sorry` at these locations
2. Previous session notes mention these as "needs symmetry lemma"
3. There are comments indicating missing infrastructure

### If Symmetry Exists: Implement Helper Lemma

Once SP confirms the mathematical validity:
1. Implement the appropriate symmetry lemma
2. Apply it to close both splitter goals
3. Verify downstream proofs complete

---

## Current Status: No Regression

### ✅ Accomplishments

1. **JP's splitter lemmas added** (lines 7247-7278)
2. **No new errors introduced** (23 errors = baseline)
3. **Infrastructure ready** for future sum manipulations
4. **Root cause identified** for splitter closure blocker

### ⏸️ Blocked Pending Mathematical Resolution

**Cannot proceed with splitter closure** until:
- SP confirms symmetry exists, OR
- Alternative proof strategy identified, OR
- Goal structure revised

---

## Files Modified This Session

**Riemann.lean**:
- Lines 1663-1673: `sumIdx_factor_const_from_sub_right` (Paul's packing lemma)
- Lines 7237-7245: Hygiene documentation
- Lines 7247-7278: JP's ΓΓ splitter lemmas (b-branch and a-branch)

**Build Logs**:
- `build_jp_splitters_oct29.txt`: Clean build with 23 errors (baseline maintained)

---

## Next Steps for JP/Paul

### Option A: Provide Symmetry Lemma

If the mathematical identity exists, provide:
```lean
lemma Γtot_sum_symmetry_μν (M r θ : ℝ) (μ ν a b : Idx) :
  sumIdx (fun e => Γtot M r θ b ν e * Γtot M r θ e μ a) =
  sumIdx (fun e => Γtot M r θ b μ e * Γtot M r θ e ν a) := by
  -- proof here
```

### Option B: Revise Proof Strategy

If the symmetry doesn't exist, the quartet split approach may need revision.

### Option C: Check for Algebraic Error

Verify that the goal state setup is correct. The sign flip (A - B vs B - A) might indicate an upstream error in how terms were manipulated.

---

**Prepared by**: Claude Code
**Session**: October 29, 2025
**Status**: Awaiting mathematical guidance for splitter closure strategy
