# Diagnostic: Tactical Fix Attempt - October 30, 2025

**Date**: October 30, 2025
**File**: Riemann.lean line 1757
**Status**: ❌ **BLOCKED** - Type mismatch in sum splitting
**Build log**: `build_tactical_fix_oct30.txt`

---

## Executive Summary

Attempted to fix the tactical elaboration error by replacing `simpa using this` with `exact this` at lines 1757 and 1766. However, this revealed a deeper issue: a **type mismatch** in how `sumIdx_add3` splits the payload terms.

**Error count**: Still 25 errors (same as before)

---

## The Error (Line 1757)

```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:1757:4: Type mismatch
  this
has type
  (sumIdx fun i =>
      -dCoord μ (fun r θ => g M i b r θ) r θ * Γtot M r θ i ν a +
          dCoord ν (fun r θ => g M i b r θ) r θ * Γtot M r θ i μ a +
        (-dCoord μ (fun r θ => g M a i r θ) r θ * Γtot M r θ i ν b +
          dCoord ν (fun r θ => g M a i r θ) r θ * Γtot M r θ i μ b)) =
    ((sumIdx fun e => -dCoord μ (fun r θ => g M e b r θ) r θ * Γtot M r θ e ν a) +
        sumIdx fun e => dCoord ν (fun r θ => g M e b r θ) r θ * Γtot M r θ e μ a) +
      sumIdx fun e =>
        -dCoord μ (fun r θ => g M a e r θ) r θ * Γtot M r θ e ν b +
          dCoord ν (fun r θ => g M a e r θ) r θ * Γtot M r θ e μ b
but is expected to have type
  (sumIdx fun e =>
      -dCoord μ (fun r θ => g M e b r θ) r θ * Γtot M r θ e ν a +
            dCoord ν (fun r θ => g M e b r θ) r θ * Γtot M r θ e μ a -
          dCoord μ (fun r θ => g M a e r θ) r θ * Γtot M r θ e ν b +
        dCoord ν (fun r θ => g M a e r θ) r θ * Γtot M r θ e μ a) =
    ((sumIdx fun e => -dCoord μ (fun r θ => g M e b r θ) r θ * Γtot M r θ e ν a) +
        sumIdx fun e => dCoord ν (fun r θ => g M e b r θ) r θ * Γtot M r θ e μ a) +
      ...
```

---

## Root Cause Analysis

### The Issue: Sign/Grouping Mismatch

**What `sumIdx_add3` produces** (has type):
- First 3 terms split correctly
- Last 2 terms **grouped in parentheses**: `(-term3 + term4)`

**What we need** (expected type):
- First 3 terms split
- Last 2 terms **written individually**: `- term3 + term4`

### Why This Matters

The type system sees these as different:
1. `sumIdx (fun e => (-a + b))` - Last two terms grouped
2. `sumIdx (fun e => -a + b)` - Last two terms individual

Even though they're mathematically equal, Lean needs exact syntactic match for the type to be correct.

---

## The Proof Structure (Lines 1751-1757)

```lean
-- Use sumIdx_add3 to split the first three terms out.
have := sumIdx_add3
          (fun e => -(dCoord μ (fun r θ => g M e b r θ) r θ) * Γtot M r θ e ν a)
          (fun e =>  (dCoord ν (fun r θ => g M e b r θ) r θ) * Γtot M r θ e μ a)
          (fun e => -(dCoord μ (fun r θ => g M a e r θ) r θ) * Γtot M r θ e ν b
                   + (dCoord ν (fun r θ => g M a e r θ) r θ) * Γtot M r θ e μ b)
exact this
```

**Problem**: The third argument to `sumIdx_add3` is itself a sum of two terms `(-term3 + term4)`. This causes `sumIdx_add3` to produce:

```
sumIdx term1 + sumIdx term2 + sumIdx (fun e => -term3 + term4)
```

But the expected type has:
```
sumIdx term1 + sumIdx term2 + sumIdx (-term3) + sumIdx term4
```

---

## Possible Solutions

### Option 1: Use `sumIdx_add4` (If Available)

If there's a `sumIdx_add4` lemma that splits 4 terms at once:
```lean
have := sumIdx_add4
          (fun e => -(dCoord μ ...) * Γtot ...)
          (fun e =>  (dCoord ν ...) * Γtot ...)
          (fun e => -(dCoord μ ...) * Γtot ...)
          (fun e =>  (dCoord ν ...) * Γtot ...)
exact this
```

### Option 2: Split in Two Steps

First apply `sumIdx_add3` to split first 3 terms, then apply `sumIdx_add_distrib` to split the grouped pair:
```lean
-- Step 1: Split first 3 terms
have h_step1 := sumIdx_add3
  (fun e => -(dCoord μ ...) * Γtot ...)
  (fun e =>  (dCoord ν ...) * Γtot ...)
  (fun e => -(dCoord μ ...) * Γtot ... + (dCoord ν ...) * Γtot ...)

-- Step 2: Split the last grouped pair
have h_step2 := sumIdx_add_distrib
  (fun e => -(dCoord μ ...) * Γtot ...)
  (fun e =>  (dCoord ν ...) * Γtot ...)

-- Step 3: Combine
rw [h_step1, h_step2]
```

But this requires careful rewriting to get the associativity right.

### Option 3: Manual Proof with Explicit Type Annotations

Add explicit type annotations to force the correct grouping:
```lean
have h₁ : (sumIdx (fun e => term1 + term2 + term3 + term4))
        = sumIdx term1 + sumIdx term2 + sumIdx term3 + sumIdx term4 := by
  -- Proof here
```

---

## Current Code Location

**File**: Riemann.lean
**Lines 1696-1772**: `payload_split_and_flip` lemma
**Lines 9225-9252**: Assembly code using the lemma

---

## What Was Attempted

1. **Replaced `simpa using this` with `exact this`** at line 1757
   - **Result**: Revealed the type mismatch instead of hiding it
2. **Replaced `simpa using sumIdx_add_distrib` with `exact sumIdx_add_distrib`** at line 1766
   - **Result**: No error here (this one is fine)

---

## Request to JP

The issue is in the proof structure of `payload_split_and_flip` lemma. Specifically:

**At lines 1752-1757**, the call to `sumIdx_add3` with three arguments results in:
- First two terms split correctly
- Third argument (which is itself a sum of two terms) stays grouped

**Needed**: Either:
1. A different splitting strategy (use `sumIdx_add4` if available, or split in multiple steps)
2. Adjustments to how the terms are grouped before splitting
3. Explicit type annotations to force correct grouping

**Current approaches tried**:
- ✅ Fixed `simpa` tactical issue (revealed underlying type problem)
- ❌ Type mismatch remains in sum splitting logic

---

## Build Status

**Command**: `lake build Papers.P5_GeneralRelativity.GR.Riemann`
**Errors**: 25 (same as baseline with original `simpa` tactical error)
**File compiles**: ❌ NO

---

## Files Modified in This Session

1. **Riemann.lean:1757**: Changed `simpa using this` → `exact this`
2. **Riemann.lean:1766**: Changed `simpa using sumIdx_add_distrib` → `exact sumIdx_add_distrib`

---

## Next Steps

**Immediate**: Wait for JP's guidance on correct proof structure for splitting the 4-term sum

**Possible approaches**:
- Use a different splitting lemma (e.g., `sumIdx_add4`)
- Split in two stages with careful rewriting
- Adjust how terms are grouped before applying `sumIdx_add3`

---

**Prepared by**: Claude Code (Lean 4 Assistant)
**Date**: October 30, 2025
**Build log**: `build_tactical_fix_oct30.txt` (25 errors)
**Status**: Blocked on proof structure - requires JP's tactical guidance
