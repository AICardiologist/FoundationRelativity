# Build Diagnostic: JP's Corrected Lemma Attempt

**Date**: October 27, 2025
**File**: Riemann.lean lines 11040-11093
**Lemma**: `regroup_right_sum_to_Riemann_CORRECT` (corrected version)
**Status**: ❌ Build failed with type mismatch

---

## Summary

Applied JP's corrected lemma that changes the statement from the FALSE version (`LHS = Riemann`) to the TRUE version (`LHS = Riemann - E` where E is the Γ·Γ commutator block).

After fixing syntax issues (duplicate doc comments and index order), the build still fails with a type mismatch in the final assembly step.

---

## Corrections Applied

### Fix 1: Removed Duplicate Doc Comment ✅

**Original** (lines 11040-11053):
- Two doc comments in a row
- Lean doesn't allow this

**Fixed**:
- Merged into single doc comment

### Fix 2: Corrected Index Order ✅

**Original** (my transcription error):
```lean
Γtot M r θ lam Idx.θ b    -- WRONG order
Γtot M r θ lam Idx.r b
```

**Fixed** (matches `Riemann_via_Γ₁` at line 2523-2524):
```lean
Γtot M r θ lam b Idx.θ    -- CORRECT order
Γtot M r θ lam b Idx.r
```

---

## Remaining Error

**Location**: Line 11090 (final `simpa [Hsolve] using Hsum` step)

**Error**: Type mismatch after simplification

**Has type** (from Hsum):
```lean
LHS = deriv Γ₁_r - deriv Γ₁_θ
```

**Expected type** (from goal after applying Hsolve):
```lean
LHS = RiemannUp * g_{bb} - (ΣA - ΣB)
where:
  ΣA = sumIdx (fun i => Γtot i b Idx.θ * Γ₁ i a Idx.r)
  ΣB = sumIdx (fun i => Γtot i b Idx.r * Γ₁ i a Idx.θ)
```

### Key Differences

1. **Riemann vs RiemannUp**: Expected type has `RiemannUp * g` (definition unfolded) instead of `Riemann`

2. **Γ·Γ term structure**:
   - **My goal statement** (line 11058-11060):
     ```lean
     sumIdx (fun lam =>
       Γ₁ lam a Idx.r * Γtot lam b Idx.θ
     - Γ₁ lam a Idx.θ * Γtot lam b Idx.r)
     ```
     This is: `Σ(A - B)` (sum of difference)

   - **Expected by Lean**:
     ```lean
     (sumIdx fun i => Γtot i b Idx.θ * Γ₁ i a Idx.r)
     - (sumIdx fun i => Γtot i b Idx.r * Γ₁ i a Idx.θ)
     ```
     This is: `ΣA - ΣB` (difference of sums)

3. **Multiplication order**:
   - My version: `Γ₁ * Γtot`
   - Expected: `Γtot * Γ₁`

These are **mathematically equivalent** by sum linearity and multiplication commutativity, but **syntactically different** for Lean's type checker.

---

## Root Cause Analysis

The issue is that the goal statement (lines 11057-11060) doesn't exactly match what `Riemann_via_Γ₁.symm` produces when rearranged with `eq_sub_iff_add_eq`.

When we write:
```lean
Riemann M r θ b a Idx.r Idx.θ
- sumIdx (fun lam => Γ₁ lam a Idx.r * Γtot lam b Idx.θ - ...)
```

Lean expects the Γ·Γ term structure to match exactly what appears in `Riemann_via_Γ₁`.

But `Riemann_via_Γ₁` (lines 2521-2524) has:
```lean
+ sumIdx (fun lam =>
    Γ₁ M r θ lam a Idx.r * Γtot M r θ lam β Idx.θ   -- β = b in our case
  - Γ₁ M r θ lam a Idx.θ * Γtot M r θ lam β Idx.r)
```

When you negate this (because we're subtracting the E term), you get:
```lean
- sumIdx (fun lam =>
    Γ₁ lam a Idx.r * Γtot lam b Idx.θ
  - Γ₁ lam a Idx.θ * Γtot lam b Idx.r)
```

Which can distribute the negation to:
```lean
- sumIdx (fun lam => Γ₁ lam a Idx.r * Γtot lam b Idx.θ)
+ sumIdx (fun lam => Γ₁ lam a Idx.θ * Γtot lam b Idx.r)
```

Or:
```lean
sumIdx (fun lam => Γ₁ lam a Idx.θ * Γtot lam b Idx.r)
- sumIdx (fun lam => Γ₁ lam a Idx.r * Γtot lam b Idx.θ)
```

**This is the difference of sums form that Lean expects!**

---

## Possible Solutions

### Option A: Change Goal Statement to Match Expected Form

Rewrite lines 11057-11060 to use difference of sums:
```lean
=
  Riemann M r θ b a Idx.r Idx.θ
  - ( sumIdx (fun lam => Γ₁ M r θ lam a Idx.r * Γtot M r θ lam b Idx.θ)
    - sumIdx (fun lam => Γ₁ M r θ lam a Idx.θ * Γtot M r θ lam b Idx.r) )
```

But this requires parentheses and might introduce additional issues.

### Option B: Add Intermediate Step to Rewrite Γ·Γ Form

Before `simpa [Hsolve] using Hsum`, add a step that proves:
```lean
sumIdx (fun lam => A - B) = sumIdx A - sumIdx B
```

This is `sumIdx_sub` or `sum_sub_distrib` in Mathlib.

### Option C: Simplify the Final Step

Instead of `simpa [Hsolve] using Hsum`, use:
```lean
rw [Hsum, Hsolve]
```

Or:
```lean
calc LHS = dΓ₁_r - dΓ₁_θ := Hsum
       _ = Riemann - Σ(...) := Hsolve
```

### Option D: Ask JP for Clarification

JP's original drop-in may have assumed certain auxiliary lemmas or a different goal structure. Request clarification on the exact goal statement and proof steps.

---

## Recommendation

**Immediate action**: Report to user that JP's corrected lemma has a structural mismatch that prevents compilation.

**Next step**: Either:
1. Try Option C (simpler final step) to see if calc chain works
2. Request JP provide the exact compiled version that worked in their environment
3. Accept that this lemma requires additional tactical work beyond what was provided

The mathematical statement is TRUE (per Senior Professor verification), but the Lean proof requires matching the exact syntactic form of `Riemann_via_Γ₁`.

---

## Current State

- **Proof #1** (`sum_k_prod_rule_to_Γ₁`): ✅ 100% COMPLETE
- **Proof #2** (`regroup_right_sum_to_Riemann_CORRECT`): ❌ Compilation blocked by type mismatch

**Sorry count**: Still 9 (Proof #2 still has sorry)

**Critical path**: ✅ UNAFFECTED (Option C Four-Block Strategy is independent)

---

**Prepared By**: Claude Code (Sonnet 4.5)
**Build Output**: `/tmp/build_jp_corrected_v2_oct27.txt`
**Exit Code**: 1 (failure)
