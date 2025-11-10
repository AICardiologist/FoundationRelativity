# Report to JP: Quick Wins Progress & Tactical Blocker (October 27, 2025)

**From**: Claude Code (Sonnet 4.5)
**To**: JP (Lean Expert)
**Status**: ✅ Major progress on recursion, ⚠️ Blocker on bb/aa_core_final
**Errors**: 14 → 9 (with 2 sorries)

---

## Executive Summary

**Great News**: ✅ **Maximum recursion depth error COMPLETELY ELIMINATED** - your primary concern is resolved!

**Blocker**: bb_core_final and aa_core_final require proving equalities between Christoffel symbol products that are NOT equal by AC (associativity-commutativity) alone. Need guidance on approach.

---

## ✅ Success: Recursion Error ELIMINATED

### Problem (Lines 7519-7569)
Your diagnostic identified recursion in first_block and second_block of ΓΓ_quartet_split_a:
```lean
have first_block := ...
have h := sub_congr H₁ H₂
simpa [sumIdx_map_sub] using h  -- ← CAUSED RECURSION
```

### Solution Implemented
Replaced with explicit calc chain using bounded simp:
```lean
have first_block :=
  calc sumIdx (fun ρ => sumIdx (fun e =>
         ((Γtot M r θ ρ μ b * Γtot M r θ e ν ρ)
        - (Γtot M r θ ρ ν b * Γtot M r θ e μ ρ)) * g M e a r θ))
    = sumIdx (fun ρ =>
        (sumIdx (fun e => (Γtot M r θ ρ μ b * Γtot M r θ e ν ρ) * g M e a r θ)) -
        (sumIdx (fun e => (Γtot M r θ ρ ν b * Γtot M r θ e μ ρ) * g M e a r θ))) := by
          apply sumIdx_congr; intro ρ
          simp only [sumIdx_map_sub, sub_mul]  -- ← BOUNDED
    _ = (sumIdx (fun ρ => sumIdx (fun e => (Γtot M r θ ρ μ b * Γtot M r θ e ν ρ) * g M e a r θ))) -
        (sumIdx (fun ρ => sumIdx (fun e => (Γtot M r θ ρ ν b * Γtot M r θ e μ ρ) * g M e a r θ))) := by
          rw [sumIdx_map_sub]
    _ = (g M a a r θ * sumIdx (fun ρ => Γtot M r θ ρ μ b * Γtot M r θ a ν ρ)) -
        (g M a a r θ * sumIdx (fun ρ => Γtot M r θ ρ ν b * Γtot M r θ a μ ρ)) := h
    _ = g M a a r θ *
          ( sumIdx (fun ρ => Γtot M r θ ρ μ b * Γtot M r θ a ν ρ)
          - sumIdx (fun ρ => Γtot M r θ ρ ν b * Γtot M r θ a μ ρ) ) := by ring
```

Similar explicit calc for second_block using sumIdx_reduce_by_diagonality.

**Result**: ✅ **Zero recursion errors** - compiles cleanly!

---

## ✅ Success: Metric Symmetry Fix (Line 7943)

Your guidance: use g_symm_JP before ring.

**Implemented**:
```lean
have fold_b :
  sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ)
    = Riemann M r θ b a μ ν := by
  have hcomm :
    sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ)
      = sumIdx (fun ρ => g M b ρ r θ * RiemannUp M r θ ρ a μ ν) := by
    apply sumIdx_congr; intro ρ
    rw [g_symm_JP M r θ ρ b]  -- ← ADDED
    ring
  simpa [Riemann, hcomm]
```

**Result**: ✅ Clean fix, error eliminated

---

## ⚠️ Blocker: bb_core_final and aa_core_final

### The Problem

**bb_core_final** (line 7395-7402):
```lean
have bb_core_final :
  g M b b r θ *
    ( sumIdx (fun e => Γtot M r θ e μ a * Γtot M r θ b ν e)
    - sumIdx (fun e => Γtot M r θ e ν a * Γtot M r θ b μ e) )
  =
  g M b b r θ *
    ( sumIdx (fun e => Γtot M r θ b μ e * Γtot M r θ e ν a)
    - sumIdx (fun e => Γtot M r θ b ν e * Γtot M r θ e μ a) )
```

**Mathematical Question**: Is this claiming:
```
Σ_e (Γ^e_μa · Γ^b_νe) = Σ_e (Γ^b_μe · Γ^e_νa)
```

These involve **different Christoffel symbols** (different index positions), so they're not equal by scalar commutativity alone.

### Tactics Tried

#### Attempt 1: Using `ring`
```lean
have swap : ∀ e, (Γtot M r θ e μ a * Γtot M r θ b ν e)
                =  (Γtot M r θ b ν e * Γtot M r θ e μ a) := by intro e; ring
simp_rw [swap, swap']; ring
```
**Result**: ❌ Creates wrong goal in calc context (introduces negation)

#### Attempt 2: Using `ac_rfl`
```lean
have h₁ :
  sumIdx (fun e => Γtot M r θ e μ a * Γtot M r θ b ν e)
    = sumIdx (fun e => Γtot M r θ b μ e * Γtot M r θ e ν a) := by
  apply sumIdx_congr; intro e; ac_rfl
```
**Result**: ❌ `Tactic 'rfl' failed: equality lhs` - confirms NOT an AC equality

#### Attempt 3: Using `congr 1` + rewrites
```lean
congr 1
have h₁ := [as above using ring]
have h₂ := [as above using ring]
rw [h₁, h₂]
```
**Result**: ❌ Unsolved goal after rewrites

### Current Status

Temporarily using `sorry` for both bb_core_final and aa_core_final:
```lean
have bb_core_final :
  g M b b r θ * ( [LHS terms] ) = g M b b r θ * ( [RHS terms] ) := by
  -- TODO: Need mathematical identity or different approach
  -- These are NOT equal by AC alone since they involve different Γ terms
  sorry
```

**Impact**: With these 2 sorries, build succeeds with **9 errors** (down from 14), confirming these unblock downstream progress.

---

## Questions for JP

### Q1: Mathematical Identity?
Is there a Christoffel symbol property that makes:
```
Γ^e_μa · Γ^b_νe = Γ^b_μe · Γ^e_νa
```

Or is this equality expected to follow from some symmetry of Γ in the Schwarzschild case?

### Q2: Structural Alternative?
Should bb_core_final and aa_core_final be proven via:
- A different factorization of the calc chain?
- Using the full context of the surrounding calc instead of isolating these equalities?
- A helper lemma that combines the terms differently?

### Q3: Original Code?
In Paul's original code before the Four-Block refactor, were these identities:
- Proven with specific lemmas?
- Part of a larger proof that didn't isolate them?
- Handled via a different structural approach?

### Q4: Tactical Guidance
If these equalities ARE mathematically valid but tactically difficult:
- Should I try `omega`, `polyrith`, or other powerful tactics?
- Is there a clever rewrite sequence using existing lemmas?
- Should I add these as axioms and come back after branches_sum?

---

## What's Working (Infrastructure)

### ✅ Calc Chains
- first_block (lines 7506-7530): ✅ Compiles with explicit calc
- second_block (lines 7532-7550): ✅ Compiles with diagonality lemma
- bb_core_reindexed (line 7385-7392): ✅ Works with `simpa using rfl`
- aa_core_reindexed (line 7567-7574): ✅ Works with `simpa using rfl`

### ✅ Helper Lemmas
- sumIdx_reduce_by_diagonality: Works perfectly in second_block
- sub_congr: Handles subtraction lifting correctly
- sumIdx_map_sub: Works when bounded with `simp only`

---

## Remaining Errors (9 total)

**With bb/aa_core_final as sorry**:

| Lines | Type | Root Cause |
|-------|------|------------|
| 8238, 8255, 8264, 8289, 8327, 8337, 8346 | unsolved goals / type mismatch | Downstream from `branches_sum` sorry (7865) |
| 2 build system | "Lean exited", "build failed" | Build errors |

**Expected**: The 7 downstream errors should vanish when branches_sum is completed.

---

## Recommended Next Steps

### Option A: Investigate Γ Properties (Your guidance needed)
- Understand if bb/aa_core_final equalities are mathematically true
- Identify which Schwarzschild Γ symmetries apply
- Prove as separate helper lemmas if needed

### Option B: Restructure Calc (Your architectural guidance)
- Maybe the calc chain shouldn't isolate these intermediate steps?
- Fold bb_core_final directly into the larger calc?
- Use a different factorization that avoids these problematic rewrites?

### Option C: Accept Sorries For Now (Pragmatic)
- Focus on completing branches_sum (the bigger blocker)
- 7 downstream errors will vanish once branches_sum is done
- Return to bb/aa_core_final with fresh perspective

---

## What You Asked For (Status)

From your drop-in fixes document:

### ✅ Fix 1: Quartet Splitter Recursion (Line 7519)
**Status**: ✅ **COMPLETE** - Used explicit calc chains with bounded simp
**Impact**: Maximum recursion depth error **ELIMINATED**

### ⚠️ Fix 2: Quartet Splitter bb_core_final (Line 7402)
**Status**: ⚠️ **BLOCKED** - Need guidance on Γ equality
**Impact**: Currently using sorry (2 errors → sorry)

### ⚠️ Fix 3: Quartet Splitter aa_core_final (Line 7583)
**Status**: ⚠️ **BLOCKED** - Same issue as bb_core_final
**Impact**: Currently using sorry

### ✅ Fix 4: Metric Symmetry (Line 7943)
**Status**: ✅ **COMPLETE** - Added g_symm_JP rewrite
**Impact**: Clean fix, error eliminated

---

## Build Verification

**Before quick wins**: 14 errors
**After recursion fix**: 12 errors
**After metric fix**: 11 errors
**With bb/aa sorries**: 9 errors

**Confirmed**: The recursion elimination is real and permanent! 🎉

---

## Request for Guidance

JP, your recursion fix worked perfectly - explicit calc chains with bounded simp eliminated the recursion completely. Thank you!

Now I need your guidance on bb_core_final and aa_core_final:

1. **Mathematical**: Are these Γ equalities expected to hold?
2. **Tactical**: If yes, what's the Lean 4 approach to prove them?
3. **Structural**: If no, should the calc be restructured to avoid them?

I've documented exactly what I tried and why each approach failed. With your guidance, I can either:
- Prove these properly (if there's a mathematical identity I'm missing)
- Restructure the calc (if this factorization is wrong)
- Move forward with sorries (if these are lower priority than branches_sum)

What direction would you recommend?

---

**Prepared by**: Claude Code (Sonnet 4.5)
**Date**: October 27, 2025
**Session**: Quick Wins Implementation
**Key Achievement**: ✅ Maximum recursion depth error ELIMINATED
**Current Blocker**: bb/aa_core_final Γ equality proofs

---

**END OF REPORT TO JP**
