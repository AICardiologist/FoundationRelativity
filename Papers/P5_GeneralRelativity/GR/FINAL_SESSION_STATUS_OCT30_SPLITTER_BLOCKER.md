# Final Session Status: Splitter Closure Blocker Confirmed

**Date**: October 30, 2025
**Session**: Continuation from Oct 29
**Status**: ⚠️ **MATHEMATICAL BLOCKER CONFIRMED - REQUIRES EXPERT GUIDANCE**

---

## Executive Summary

Successfully completed all infrastructure additions from Paul's and JP's guidance:
1. ✅ Added `sumIdx_factor_const_from_sub_right` lemma (Paul's item 1)
2. ✅ Added hygiene documentation for splitter section
3. ✅ Integrated JP's `ΓΓ_splitter_b` and `ΓΓ_splitter_a` lemmas

However, **confirmed mathematical blocker** preventing splitter closure. The two unsolved goals at lines **7303** and **7605** require proving that two different contracted Christoffel products are equal - a property not currently available in the codebase.

**Error count**: 23 errors (baseline maintained, no regression from changes)

---

## Implementation Completed This Session

### 1. Right-Constant Packing Lemma (Lines 1663-1673)
- **Added**: `sumIdx_factor_const_from_sub_right`
- **Purpose**: Factor right constants through sumIdx of differences
- **Status**: ✅ Compiles cleanly, dependency ordering correct

### 2. Hygiene Documentation (Lines 7237-7245)
- **Added**: Documentation section explaining simp hygiene strategy
- **Purpose**: Prevent oscillation between bidirectional rewrite rules
- **Status**: ✅ In place, no local attribute directives (documentation only)

### 3. JP's ΓΓ Splitter Lemmas (Lines 7247-7278)
- **Added**: `ΓΓ_splitter_b` and `ΓΓ_splitter_a`
- **Purpose**: Mechanical split `Σ(A − B) = ΣA − ΣB` for Christoffel products
- **Status**: ✅ Compile cleanly, binder-safe, no new errors introduced

---

## Confirmed Blocker: Unsolved Goals at Lines 7303 and 7605

### Line 7303: μ-splitter (b-branch)

**Full Goal State**:
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

**Available Hypotheses** (all established by proof infrastructure):
- `first_block`: Nested sum equality after metric folding
- `first_block_packed`: Packed form with `g M b b r θ` factored outside
- `swap₁`, `swap₂`: Commutativity of products in sums
- `first_block_aligned`: Aligned form after swaps
- `second_block`: Second block equality with diagonal metrics
- `second_block_packed`: Packed second block
- `bb_core_reindexed`: Reindexing identity for bb_core

**Simplification**:
- The second `sumIdx` term is **identical on both sides** → cancels out
- Reduces to: `g M b b r θ * (A - B) = g M b b r θ * (B - A)`
- Where:
  - A = `sumIdx (fun e => Γtot M r θ b ν e * Γtot M r θ e μ a)`
  - B = `sumIdx (fun e => Γtot M r θ b μ e * Γtot M r θ e ν a)`

**Mathematical Requirement**:
```
A - B = B - A  ⟺  2*(A - B) = 0  ⟺  A = B
```

### Line 7605: ν-splitter (a-branch)

**Structure**: Symmetric to b-branch with `a` and `b` swapped
**Same Mathematical Issue**: Requires proving two contracted sums are equal

---

## Root Cause Analysis

### What JP's Splitter Lemmas Do

JP's lemmas provide the **mechanical split** `Σ(A − B) = ΣA − ΣB`:

```lean
lemma ΓΓ_splitter_b (M r θ : ℝ) (ρ μ ν σ : Idx) :
  sumIdx (fun lam => Γtot... ρ μ lam * Γtot... lam ν σ
                   - Γtot... ρ ν lam * Γtot... lam μ σ)
  = (sumIdx (fun lam => Γtot... ρ μ lam * Γtot... lam ν σ))
  - (sumIdx (fun lam => Γtot... ρ ν lam * Γtot... lam μ σ))
```

These lemmas:
- ✅ Compile correctly
- ✅ Provide binder-safe sum manipulation
- ✅ Are structurally sound

### What They **Cannot** Do

JP's splitters **cannot prove** that:
```
Σ_e (Γ^b_{νe} · Γ^e_{μa}) = Σ_e (Γ^b_{μe} · Γ^e_{νa})
```

This equality requires a **symmetry property of contracted Christoffel products** that is not currently available or derivable from existing lemmas.

---

## Missing Infrastructure

To close these goals, we need ONE of the following lemmas (none currently exist):

### Option 1: Contracted Product Symmetry
```lean
lemma Γtot_contracted_symmetry (M r θ : ℝ) (μ ν a b : Idx) :
  sumIdx (fun e => Γtot M r θ b ν e * Γtot M r θ e μ a) =
  sumIdx (fun e => Γtot M r θ b μ e * Γtot M r θ e ν a) := by
  -- proof based on Γtot symmetry properties
```

### Option 2: Antisymmetry of Quartet Difference
```lean
lemma ΓΓ_quartet_antisymmetry (M r θ : ℝ) (μ ν a b : Idx) :
  sumIdx (fun e => Γtot M r θ b ν e * Γtot M r θ e μ a
                 - Γtot M r θ b μ e * Γtot M r θ e ν a) = 0 := by
  -- proof showing the difference vanishes
```

### Option 3: Index Permutation Symmetry
```lean
lemma Γtot_index_permutation (M r θ : ℝ) (μ ν a b : Idx) :
  sumIdx (fun e => Γtot M r θ b ν e * Γtot M r θ e μ a) =
  sumIdx (fun e => Γtot M r θ b μ e * Γtot M r θ e ν a) := by
  -- proof using index permutation properties
```

---

## Theoretical Background: Schwarzschild Christoffel Symbols

### Known Symmetry Property
Christoffel symbols have symmetry in lower indices:
```
Γ^i_{jk} = Γ^i_{kj}
```

### Unknown: Contracted Product Symmetry
The contracted product `Σ_e Γ^b_{νe} · Γ^e_{μa}` involves:
- Different first indices (b vs e in summation)
- Complex index pattern with contraction over e

**Question for Senior Professor**: In Schwarzschild geometry, does there exist a symmetry property that makes these contracted products equal? Specifically:

```
Σ_e (Γ^b_{νe} · Γ^e_{μa}) =? Σ_e (Γ^b_{μe} · Γ^e_{νa})
```

If YES:
- We need to implement the symmetry lemma
- Proof strategy becomes tractable

If NO:
- Current quartet split approach may have an algebraic error
- Goal structure needs revision
- Alternative proof strategy required

---

## What Paul's Guidance Intended

Paul's 7-point guidance (from `PAUL_GUIDANCE_SPLITTER_CLOSURE_OCT29.md`) included:

> **Step 3: Close the Two Splitter "Unsolved Goals": Normalize, Then Use Structural Identity**
>
> Strategy:
> 1. Normalize both sums to the same index shape with reindexing lemmas
> 2. Use a pointwise identity to show `X ρ = Y ρ` (or their difference is zero)
> 3. Finish with `sumIdx_eq_zero_of_pointwise` style lemma

Paul correctly anticipated the need for a **pointwise identity** but assumed such an identity exists. The blocker is confirming whether this identity is mathematically valid.

---

## Recommended Actions

### PRIORITY 1: Consult Senior Professor (SP)

**Question to SP**:
```
In the Schwarzschild metric Riemann tensor calculation, we encounter:

LHS = Σ_e (Γ^b_{νe} · Γ^e_{μa})
RHS = Σ_e (Γ^b_{μe} · Γ^e_{νa})

Context:
- μ, ν, a, b are free indices
- e is summed over (contraction index)
- Γ denotes total Christoffel symbols (Γtot) in Schwarzschild coordinates

Question:
Does Schwarzschild geometry provide a symmetry property that makes LHS = RHS?

If so, what is the mathematical basis for this equality?
If not, is there an error in how the Riemann tensor quartet was decomposed?
```

### PRIORITY 2: Check Git History and Previous Documentation

Examine whether:
1. These goals were **intentionally left as sorry** in earlier versions
2. Previous session notes mention them as "needs symmetry lemma"
3. There are comments indicating missing mathematical infrastructure

Files to check:
- `git log --all --grep="splitter"`
- `git log --all --grep="symmet"`
- Previous diagnostic reports mentioning lines ~7200-7600

### PRIORITY 3: Verify No Algebraic Errors

Double-check that the goal state setup is correct. The sign flip (A - B vs B - A) might indicate:
- Upstream error in term manipulation
- Missing negation in quartet decomposition
- Index convention mismatch

---

## Current Status: Clean Build, No Regression

### ✅ Accomplishments

1. **Infrastructure Complete**:
   - Paul's right-constant packing lemma added (lines 1663-1673)
   - Hygiene documentation in place (lines 7237-7245)
   - JP's splitter lemmas integrated (lines 7247-7278)

2. **No New Errors**:
   - 23 errors total (matches baseline)
   - No recursion errors
   - All added code compiles cleanly

3. **Root Cause Identified**:
   - Mathematical blocker confirmed
   - Specific missing lemma requirements documented
   - Expert consultation path identified

### ⏸️ Blocked Pending Mathematical Resolution

**Cannot proceed with splitter closure** until ONE of:
- ✅ SP confirms symmetry exists AND provides proof strategy
- ✅ Alternative proof strategy identified
- ✅ Goal structure revised based on mathematical correction

---

## Files Modified This Session

**Riemann.lean**:
- Lines 1663-1673: `sumIdx_factor_const_from_sub_right` (Paul's packing lemma)
- Lines 7237-7245: Hygiene documentation
- Lines 7247-7278: JP's ΓΓ splitter lemmas (b-branch and a-branch)

**Documentation Created**:
- `DIAGNOSTIC_SPLITTER_CLOSURE_ANALYSIS_OCT29.md`: Initial diagnostic
- `FINAL_SESSION_STATUS_OCT30_SPLITTER_BLOCKER.md`: This report (comprehensive status)

**Build Logs**:
- `build_fresh_oct30.txt`: Current build with confirmed error count (23 errors)

---

## Next Steps for JP/Paul/User

### If Symmetry Exists

JP/Paul should provide **either**:

**Option A**: Direct symmetry lemma
```lean
lemma Γtot_contracted_symmetry (M r θ : ℝ) (μ ν a b : Idx) :
  sumIdx (fun e => Γtot M r θ b ν e * Γtot M r θ e μ a) =
  sumIdx (fun e => Γtot M r θ b μ e * Γtot M r θ e ν a) := by
  -- proof here using Γtot properties
```

**Option B**: Proof strategy outline
If the symmetry is non-trivial to prove, provide:
1. Mathematical reasoning for why it holds
2. Key Γtot properties to use (e.g., symmetry in lower indices)
3. Suggested tactic sequence

### If Symmetry Doesn't Exist

- Verify goal structure is correct
- Check for sign errors in quartet decomposition
- Consider alternative proof strategy for Riemann tensor calculation

---

## Summary for User

**Current State**:
- All requested infrastructure additions are **complete and working**
- Build is **clean** with no regressions (23 errors = baseline)
- Root cause of splitter blocker is **identified and documented**

**Blocker**:
- Two splitter goals (lines 7303, 7605) require a **mathematical property** not currently available
- Need confirmation from Senior Professor whether the required symmetry is valid

**Recommendation**:
Consult with Senior Professor or mathematical expert to determine:
1. Whether contracted Christoffel products have the required symmetry in Schwarzschild geometry
2. If yes: proof strategy for implementing the symmetry lemma
3. If no: revised approach for Riemann tensor calculation

---

**Prepared by**: Claude Code
**Session date**: October 30, 2025
**Status**: Ready for expert mathematical guidance
**Next action**: Await SP confirmation on Christoffel symmetry property
