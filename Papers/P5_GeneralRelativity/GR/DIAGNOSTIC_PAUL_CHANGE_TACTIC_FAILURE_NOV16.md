# Diagnostic Report: Paul's "Truly AC-Free" Fix with `change` Tactic FAILED - November 16, 2024

**Status**: ❌ **BUILD FAILS - 15 errors**
**For**: Paul (Tactic Professor)
**From**: Claude Code
**Date**: November 16, 2024

---

## Executive Summary

Paul's fourth fix attempt using `change` + `exact` pattern has **FAILED** with 15 errors:

- **Primary failure**: `'change' tactic failed, pattern` at line 8989
- **Root cause**: **Parenthesization mismatch** between `B_b` definition and `change` pattern
- **Build status**: **FAILS** ❌
- **Error progression**: 17 → 15 → 18 → 19 → **15 errors** (all four fix attempts failed)

The `change` tactic requires exact syntactic equality, but:
- `B_b` definition groups as: `(a + b + c) - d`
- `change` pattern expects: `(a + b) + (c - d)`

These are **mathematically equal** but **not definitionally equal** in Lean 4.

---

## 1. Error Count Summary

| Fix Attempt | Date | Errors | Status | Method |
|-------------|------|--------|--------|--------|
| Baseline | Nov 14 | 17 | ❌ | Pre-existing |
| First Paul fix | Nov 16 | 15 | ❌ | Added `B_b` binding |
| Second Paul fix (AC lemmas) | Nov 16 | 18 | ❌ | `simp [add_comm, ...]` |
| Third Paul fix ("AC-free" simpa) | Nov 16 | 19 | ❌ | `simpa using ...` |
| **Fourth Paul fix (change + exact)** | **Nov 16** | **15** | **❌** | **`change` pattern** |

**Trend**: All four fix attempts have failed. No progress toward resolution.

---

## 2. Primary Failure: Line 8989 - `change` Tactic Pattern Mismatch

### Error Message

```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8989:10: 'change' tactic failed, pattern
  (sumIdx fun ρ =>
      -dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ * g M ρ b r θ +
          dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ * g M ρ b r θ +
        ((g M ρ b r θ * sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a) -
          g M ρ b r θ * sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a)) =
    ((sumIdx fun ρ => -dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ * g M ρ b r θ) +
        sumIdx fun ρ => dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ * g M ρ b r θ) +
      ((sumIdx fun ρ => g M ρ b r θ * sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a) -
        sumIdx fun ρ => g M ρ b r θ * sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a)
is not definitionally equal to target
  sumIdx B_b =
    ((sumIdx fun ρ => -dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ * g M ρ b r θ) +
        sumIdx fun ρ => dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ * g M ρ b r θ) +
      ((sumIdx fun ρ => g M ρ b r θ * sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a) -
        sumIdx fun ρ => g M ρ b r θ * sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a)
```

### Analysis

The `change` tactic failed because the **pattern** (what we want to match) is not definitionally equal to the **target** (what Lean sees).

**Pattern LHS** (from `change` command):
```lean
sumIdx (fun ρ =>
  ( -(dCoord μ ...) * g M ρ b r θ )
  + ( (dCoord ν ...) * g M ρ b r θ )
  + ( g M ρ b r θ * sumIdx ... - g M ρ b r θ * sumIdx ... )
)
```

**Target LHS** (what Lean sees):
```lean
sumIdx B_b
```

**Where `B_b` is defined as** (lines 8956-8961):
```lean
let B_b := fun ρ =>
    (-(dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ) * g M ρ b r θ)
  + (  (dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ) * g M ρ b r θ)
  + (  g M ρ b r θ * sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a))
  - (  g M ρ b r θ * sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a))
```

---

## 3. The Parenthesization Mismatch

### Root Cause

The issue is **operator precedence and parenthesization**:

**`B_b` definition groups as**:
```
a + b + c - d
```
Which Lean parses as:
```
((a + b) + c) - d
```

**`change` pattern expects**:
```
a + b + (c - d)
```
Which is:
```
(a + b) + (c - d)
```

### Why This Matters

In Lean 4:
- `((a + b) + c) - d` is NOT definitionally equal to `(a + b) + (c - d)`
- These are **propositionally equal** (can be proven with `ring` or `ac_rfl`)
- But they are **not syntactically equal**
- The `change` tactic requires **exact syntactic match** of the pattern

### Simplified Example

```lean
-- This works:
let x := a + (b - c)
change a + (b - c) = d  -- ✅ Matches exactly

-- This fails:
let x := a + b - c
change a + (b - c) = d  -- ❌ Pattern doesn't match
-- Because: (a + b - c) is parsed as ((a + b) - c)
--          which is NOT the same as (a + (b - c))
```

---

## 4. Why Paul's Approach Was Correct in Principle but Failed in Practice

### The Strategy

Paul's strategy was sound:
1. Define `B_b` with exact same expression structure
2. Use `change` to unfold `B_b` definitionally
3. Apply `exact` with packaging lemma
4. **No `simp`, no AC lemmas, no global rewriting**

This **should** avoid all recursion issues.

### The Fatal Flaw

The implementation had a **parenthesization bug**:
- Line 8956-8961: `B_b` defined with `a + b + c - d` grouping
- Line 8990-8996: `change` pattern expects `a + b + (c - d)` grouping
- Lean cannot match these definitionally

### What Would Have Worked

If the `B_b` definition matched the `change` pattern exactly:

```lean
let B_b := fun ρ =>
    (-(dCoord μ ...) * g M ρ b r θ)
  + (  (dCoord ν ...) * g M ρ b r θ)
  + ( (  g M ρ b r θ * sumIdx ...)
    - (  g M ρ b r θ * sumIdx ...) )  -- ← Extra parens here
```

Then `change` would succeed because the pattern would match exactly.

---

## 5. All 15 Errors (Full List)

| Line | Error Type | Root Cause |
|------|------------|------------|
| 8989 | `'change' tactic failed, pattern` | **PRIMARY: Parenthesization mismatch** |
| 9070 | Type mismatch | Cascade from 8989 |
| 9072 | Unsolved goals | Cascade from 8989 |
| 8796 | Unsolved goals | Pre-existing (bb-branch) |
| 9240 | Failed to synthesize | Pre-existing |
| 9255 | Unsolved goals | Pre-existing |
| 9273 | Type mismatch | Pre-existing |
| 9277 | Tactic `rewrite` failed | Pre-existing |
| 9092 | Unsolved goals | Pre-existing |
| 9318 | Unsolved goals | Pre-existing |
| 9555 | Type mismatch | Pre-existing |
| 9756 | Type mismatch | Pre-existing |
| 9770 | Tactic `rewrite` failed | Pre-existing |
| 9839 | Unsolved goals | Pre-existing |
| 9950 | Unsolved goals | Pre-existing |

**Breakdown**:
- **3 new b-branch errors** (8989, 9070, 9072) - caused by `change` failure
- **12 pre-existing errors** - unrelated to this fix

---

## 6. Comparison with Previous "AC-Free" Attempt

| Aspect | Third Fix (simpa) | Fourth Fix (change) |
|--------|------------------|---------------------|
| Error count | 19 | 15 |
| Primary failure | Recursion in `simpa` | Pattern mismatch in `change` |
| AC lemmas used? | YES (global simp set) | NO (true AC-free) |
| Conceptually sound? | NO (misleading) | YES (correct strategy) |
| Implementation bug | Used `simpa` without args | Parenthesization mismatch |

**Verdict**: Fourth fix was conceptually superior but had an implementation bug.

---

## 7. The Fundamental Architectural Problem

### Three Incompatible Requirements

1. **Calc block type checker**: Requires exact syntactic equality of `sumIdx B_b` in LHS
2. **Packaging lemma**: Requires specific grouping `(a + b) + (c - d)` to match `sumIdx_add3_of_sub`
3. **`B_b` definition**: Natural grouping `a + b + c - d` doesn't match packaging lemma

### Why This Is Hard

- If `B_b` is defined to match packaging lemma → Extra parens look "unnatural"
- If `B_b` is defined naturally → Doesn't match packaging lemma definitionally
- Need propositional equality (`ring`) to bridge the gap → But that invokes AC lemmas
- Paul's guardrail forbids AC lemmas → **Catch-22**

---

## 8. Detailed Code Analysis

### Location: Riemann.lean:8956-9015

**`B_b` definition (lines 8956-8961)**:
```lean
let B_b := fun ρ =>
    (-(dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ) * g M ρ b r θ)
  + (  (dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ) * g M ρ b r θ)
  + (  g M ρ b r θ * sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a))
  - (  g M ρ b r θ * sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a))
  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  This is parsed as: ((a + b) + c) - d
```

**`change` pattern (lines 8990-8996)**:
```lean
change
  sumIdx (fun ρ =>
    ( -(dCoord μ ...) * g M ρ b r θ )
    + ( (dCoord ν ...) * g M ρ b r θ )
    + ( g M ρ b r θ * sumIdx ...
        - g M ρ b r θ * sumIdx ... )
    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
    This expects: (a + b) + (c - d)
  )
  = ...
```

**The mismatch**:
```
B_b grouping:      ((a + b) + c) - d
change expects:    (a + b) + (c - d)
                              ^^^^^^^^ Different!
```

---

## 9. Why Working Patterns Don't Apply

### BB-Branch Success Pattern

The bb-branch uses a different approach:
```lean
have scalar_finish_bb : ... := by
  simp [h_insert_delta_for_bb, sumIdx_delta_right]
  ring  -- ✅ AC lemmas allowed OUTSIDE calc block

calc ...
  _ = ... := by rw [← scalar_finish_bb]  -- ✅ Just reference
```

**Key difference**: All AC normalization happens **outside** the calc block, where recursion is manageable.

### Why B-Branch Can't Use This

The b-branch needs:
1. `B_b` defined **inside** calc block scope (for syntactic matching)
2. Packaging that matches `B_b` **exactly** (no AC normalization)
3. But `B_b` natural grouping ≠ packaging lemma grouping

**Result**: Cannot pre-compute helper outside calc (BB pattern), and cannot match definitionally inside calc (Paul's pattern).

---

## 10. Potential Fixes (Ordered by Viability)

### Option A: Fix Parenthesization in `B_b` Definition ⭐ **MOST DIRECT**

**Change** (line 8956-8961):
```lean
let B_b := fun ρ =>
    (-(dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ) * g M ρ b r θ)
  + (  (dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ) * g M ρ b r θ)
  + ( (  g M ρ b r θ * sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a))
    - (  g M ρ b r θ * sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a)) )
    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
    Add extra parens around (c - d)
```

**Pros**: Minimal change, preserves Paul's AC-free strategy
**Cons**: Slightly awkward syntax
**Likelihood of success**: **HIGH** (90%)

---

### Option B: Use `show` Instead of `change`

Replace `change` with `show`:
```lean
have LHS_regroup : sumIdx B_b = ... := by
  show sumIdx B_b = ...  -- Just restate the goal
  have h := (sumIdx_add3_of_sub ...).symm
  -- Now need to bridge B_b ↔ expanded form
  conv_lhs => unfold B_b  -- Unfold B_b on LHS only
  simp only []  -- Normalize parentheses WITHOUT AC lemmas
  exact h
```

**Pros**: More flexible than `change`
**Cons**: Still needs parenthesis normalization, may hit same issue
**Likelihood of success**: **MEDIUM** (50%)

---

### Option C: Use `convert` with Degree Control

```lean
have LHS_regroup : sumIdx B_b = ... := by
  convert (sumIdx_add3_of_sub ...).symm using 2
  -- Allow 2 levels of non-defeq difference
  -- Then prove remaining goals with `ring` in bounded scope
  · unfold B_b; ring
```

**Pros**: Allows controlled use of `ring` for parenthesis issues
**Cons**: Violates "no AC lemmas" guardrail
**Likelihood of success**: **HIGH** (80%), but conceptually impure

---

### Option D: Revert to Baseline and Consult Senior Professor

Revert all four failed fix attempts:
```bash
git checkout HEAD~4 -- Papers/P5_GeneralRelativity/GR/Riemann.lean
```

Then **consult with senior professor** on:
1. Is the three-phase pattern (Hpack → Hshape → Hδ) correct for b-branch?
2. Alternative approaches to sum packaging that avoid AC normalization?
3. Should b-branch use a fundamentally different proof structure?

**Pros**: Fresh start with expert guidance
**Cons**: Abandons all recent work
**Likelihood of success**: **UNKNOWN** (requires new strategy)

---

## 11. Recommended Action

### Immediate Fix: **Option A** (Fix Parenthesization)

1. **Edit line 8960-8961** to add explicit parens around `(c - d)`:
   ```lean
   + ( (  g M ρ b r θ * sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a))
     - (  g M ρ b r θ * sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a)) )
   ```

2. **Rebuild** and verify error count drops from 15 to 12 (eliminating 3 b-branch errors)

3. **If successful**: Continue with Paul's AC-free strategy for remaining errors

4. **If still fails**: Fall back to **Option C** (convert with bounded `ring`)

### Long-Term Strategy

If Option A succeeds but reveals more parenthesization issues downstream:
- **Document** all grouping requirements for sum packaging lemmas
- **Standardize** parenthesization conventions across all branches
- **Consider** adding explicit simp lemmas for grouping normalization (carefully controlled)

---

## 12. Technical Details

### Build Log
- **File**: `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/build_paul_truly_ac_free_verify_nov16.txt`
- **Total errors**: 15
- **B-branch errors**: 3 (lines 8989, 9070, 9072)
- **Pre-existing errors**: 12

### Code Locations
- **`B_b` definition**: Riemann.lean:8956-8961
- **`LHS_regroup` proof**: Riemann.lean:8975-9015
- **`change` failure**: Riemann.lean:8989
- **Helper lemmas**: Riemann.lean:1750-1771

### Error Categories
1. **Pattern mismatch** (1): Line 8989 - `change` tactic
2. **Type mismatch** (4): Lines 9070, 9273, 9555, 9756
3. **Unsolved goals** (9): Lines 9072, 8796, 9255, 9092, 9318, 9839, 9950
4. **Rewrite failed** (2): Lines 9277, 9770
5. **Failed to synthesize** (1): Line 9240

---

## 13. Conclusion

Paul's fourth fix was **conceptually correct** but failed due to a **subtle implementation bug**:

- **Strategy**: ✅ AC-free, no global simp, exact definitional matching
- **Implementation**: ❌ Parenthesization mismatch in `B_b` vs `change` pattern
- **Fix difficulty**: **EASY** - just add explicit parens in `B_b` definition
- **Confidence**: **HIGH** - this is a mechanical fix, not a conceptual issue

**Critical insight**: The `change` tactic in Lean 4 requires **exact syntactic equality**, including:
- Parenthesization
- Operator associativity
- Whitespace doesn't matter, but grouping does

**Recommended next step**: Apply Option A (fix parenthesization) and rebuild to verify.

---

**Report Completed**: November 16, 2024
**Build Log**: `build_paul_truly_ac_free_verify_nov16.txt`
**Errors**: 15 total (3 new b-branch + 12 pre-existing)
**Recommendation**: **FIX PARENTHESIZATION IN `B_b`** (Option A)
**Confidence**: **HIGH** (90% this resolves the `change` failure)
