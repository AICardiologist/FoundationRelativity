# Report to JP: Step 4½ Normalization Result

**Date**: October 30, 2025
**Re**: Four-Block assembly - Binder-safe normalization implemented, pattern mismatch persists
**Status**: ❌ **BLOCKER UNRESOLVED** - Requires strategic guidance

---

## Executive Summary

**Implemented**: Paul's Step 4½ binder-safe normalization (4 phases, all 9 normalizer lemmas)

**Result**: Error count reduced 25 → 23, BUT `payload_cancel_all` pattern mismatch **persists unchanged** at line 9164

**Root Cause**: Structural mismatch between goal state (∂Γ + payload + ΓΓ all mixed) and lemma expectation (payload only)

**Status**: Normalizers working correctly - problem is beyond their scope

---

## What Was Done

### Implementation of Paul's Guidance

Per his correction to avoid `ring_nf`, I implemented the complete 4-phase binder-safe normalization at lines 9142-9163:

```lean
-- 1) Flatten and re-associate
simp only [flatten₄₁, flatten₄₂, group_add_sub, fold_sub_right, fold_add_left]

-- 2) Pull common factors through Σ
try (simp only [sumIdx_sub_same_right, sumIdx_add_same_left])

-- 3) Coalesce quartets
try (simp only [collect_four_pairs_to_two_sums, sumIdx_collect8_unbalanced])

-- 4) Final reshaping
try (simp only [flatten₄₁, flatten₄₂, group_add_sub])

rw [payload_cancel_all M r θ h_ext μ ν a b]  -- ❌ STILL FAILS
```

All 9 normalizer lemmas verified present in Riemann.lean (lines 161-1797).

### Build Results
- **Error count**: 25 → 24 → 23 (minor syntactic issues fixed)
- **Core error**: Line 9164 pattern mismatch - **UNCHANGED**

---

## The Pattern Mismatch

### What `payload_cancel_all` Expects (Lines 8959-8973)

**ONLY** four `sumIdx` terms with index `ρ`:
```lean
  sumIdx (fun ρ => -Γtot ρ ν a * dCoord μ (g ρ b) + Γtot ρ μ a * dCoord ν (g ρ b))
+ sumIdx (fun ρ => -Γtot ρ μ a * dCoord ν (g ρ b) + Γtot ρ ν a * dCoord μ (g ρ b))
+ sumIdx (fun ρ => -Γtot ρ ν b * dCoord μ (g a ρ) + Γtot ρ μ b * dCoord ν (g a ρ))
+ sumIdx (fun ρ => -Γtot ρ μ b * dCoord ν (g a ρ) + Γtot ρ ν b * dCoord μ (g a ρ))
= 0
```

### What the Goal State Contains (From Error Message)

**Three distinct blocks** with different indices and structure:

**Block 1 (∂Γ terms)**: `sumIdx (dCoord(Γtot) * g)` with index `e`
```lean
sumIdx fun e =>
  -dCoord μ (Γtot e ν a) * g e b - dCoord μ (Γtot e ν b) * g a e +
   dCoord ν (Γtot e μ a) * g e b + dCoord ν (Γtot e μ b) * g a e
```

**Block 2 (Payload-like)**: `sumIdx (Γtot * dCoord(g))` with index `e` (NOT `ρ`)
```lean
sumIdx fun e =>
  -Γtot e ν a * dCoord μ (g e b) - Γtot e ν b * dCoord μ (g a e) +
   Γtot e μ a * dCoord ν (g e b) + Γtot e μ b * dCoord ν (g a e)
```

**Block 3 (ΓΓ double-sums)**: With index `ρ` and nested `e`
```lean
sumIdx fun ρ =>
  sumIdx fun e =>
    (Γtot ρ μ a * Γtot e ν ρ - Γtot ρ ν a * Γtot e μ ρ) * g e b
+ ...
```

**Mismatches**:
1. **Index names**: Goal uses `e`, pattern expects `ρ`
2. **Structure**: Goal has THREE blocks, pattern expects ONLY payload (four separate sums)
3. **Extra terms**: Goal contains ∂Γ and ΓΓ terms not in pattern

---

## Why Normalizers Can't Fix This

Binder-safe normalizers can:
- ✅ Reshape arithmetic (grouping, associativity, factoring)
- ✅ Pull common factors through Σ
- ✅ Flatten nested additions

Binder-safe normalizers CANNOT:
- ❌ Extract a subset of terms from larger expression
- ❌ Change index variable names (`e` → `ρ`)
- ❌ Split combined sums into separate sums
- ❌ Remove ∂Γ and ΓΓ blocks that shouldn't be matched

This is a **structural mismatch**, not a **syntactic normalization** issue.

---

## Root Cause: Assembly Strategy Assumption

### The Assumption
After steps 1-4 (unfold + expand_P_ab + expand_Ca + expand_Cb), the goal should contain terms grouped such that Block A (`payload_cancel_all`) can match and cancel just the payload terms.

### The Reality
After steps 1-4, the goal contains **ALL expanded terms** from:
- `expand_P_ab`: ∂Γ terms + P payload + P ΓΓ
- `expand_Ca`: C'_a payload + C'_a main + C'_a cross
- `expand_Cb_for_C_terms_b`: C'_b payload + C'_b main + C'_b cross

All mixed together with shared index variables.

### The Problem
`payload_cancel_all` expects to match ONLY the four payload sums **in isolation**, but they're embedded in a much larger expression.

---

## Questions for JP

### 1. Is the Original Assembly Strategy Correct?

The commented-out 8-step plan (lines 9140-9148) assumes:
```
Step 1: Unfold definitions
Step 2-4: Expand all terms
Step 5: Apply payload_cancel_all  ← FAILS HERE
Step 6-8: Apply remaining blocks
```

Should `payload_cancel_all` be applied to the **full expanded goal**, or should payload terms be **isolated first**?

### 2. What Should the Goal Look Like After Step 4?

Is the current goal state (∂Γ + payload + ΓΓ all mixed) expected, or should the expansion lemmas produce a different structure?

### 3. How to Resolve the Index Mismatch?

Goal uses `e` in payload-like terms, pattern expects `ρ`. Is this expected? Do we need:
- An index-renaming step?
- Different expansion lemmas with consistent indices?
- A version of `payload_cancel_all` that works with `e`?

### 4. Recommended Next Step?

**Option A**: Restructure assembly to isolate term groups before applying blocks

**Option B**: Modify `payload_cancel_all` to match actual goal structure (accept full expression, prove payload portion = 0)

**Option C**: Add intermediate extraction lemmas for focused rewriting

**Option D**: Manual `show (...)` coercion after InfoView inspection

**Option E**: Different approach entirely

---

## Build Status

**File**: `Riemann.lean` lines 9127-9169 (`algebraic_identity_four_block_old`)
**Error**: Line 9164 (`rw [payload_cancel_all ...]` pattern mismatch)
**Error count**: 23 (down from 25, but core blocker unchanged)
**Build log**: `build_try_wrap_oct30.txt`

### Dependencies (All Still ✅)
- `expand_P_ab`: ✅ PROVEN (lines 6599-7017, Oct 25, ZERO sorries)
- `expand_Ca`: ✅ PROVEN (lines 6517-6541)
- `expand_Cb_for_C_terms_b`: ✅ PROVEN (lines 6567-6593)
- `payload_cancel_all`: ✅ PROVEN (lines 8959-8988, Block A)
- All other blocks: ✅ PROVEN

All dependencies solid. Issue is assembly strategy, not lemma quality.

---

## Conclusion

Paul's Step 4½ binder-safe normalization was correctly implemented with all specified lemmas. The normalizers worked as designed but cannot solve this problem because it's not a normalization issue - it's a **strategic mismatch** between:
- How the expansion lemmas structure the goal (all terms mixed)
- What the block lemmas expect to match (isolated term groups)

**The Four-Block assembly cannot proceed without resolving this fundamental structural mismatch.**

**Request**: Tactical guidance on which approach (A-E above) to take for resolving this blocker.

---

**Prepared by**: Claude Code (Lean 4 Assistant)
**Date**: October 30, 2025
**Detailed diagnostic**: `DIAGNOSTIC_STEP4HALF_NORMALIZATION_FAILURE_OCT30.md`
**Priority**: **HIGH** - blocking Four-Block Strategy completion

---

## Supporting Documentation

- **Comprehensive analysis**: `DIAGNOSTIC_STEP4HALF_NORMALIZATION_FAILURE_OCT30.md`
- **Original assembly failure**: `REPORT_TO_JP_FOUR_BLOCK_ASSEMBLY_OCT30.md`
- **Build log**: `build_try_wrap_oct30.txt` (23 errors)
- **Discovery document**: `CRITICAL_DISCOVERY_OCT30_ASSEMBLY_READY.md`
- **Implementation plan**: `IMPLEMENTATION_PLAN_PAUL_GUIDANCE_OCT30.md`
