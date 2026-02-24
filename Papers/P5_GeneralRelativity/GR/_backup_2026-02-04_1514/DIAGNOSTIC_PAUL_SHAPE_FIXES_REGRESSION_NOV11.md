# DIAGNOSTIC REPORT: Paul's Shape Fixes Implementation - November 11, 2025

**Status**: ❌ **REGRESSION**
**Error Count**: 13 → 18 errors (5 error increase)
**For**: Paul
**From**: Claude Code
**Severity**: MEDIUM - Shape adapter lemmas causing new issues

---

## Executive Summary

Attempted to implement Paul's shape mismatch fixes by adding g_swap lemma and commuted δ-insertion lemmas. Build completed but with **18 errors** (up from 13), indicating implementation issues with the syntactic adapters.

---

## What Was Implemented

Based on Paul's guidance, I added:

### 1. g_swap Lemma (lines 1741-1743)
```lean
@[simp] lemma g_swap (M r θ : ℝ) (i j : Idx) :
  g M i j r θ = g M j i r θ := by
  cases i <;> cases j <;> simp [g]
```

### 2. Commuted δ-insertion Lemmas (lines 1812-1841)

**insert_delta_right_diag_comm**:
```lean
@[simp] lemma insert_delta_right_diag_comm
    (M r θ : ℝ) (b : Idx) (F : Idx → ℝ) :
  sumIdx (fun ρ => g M ρ b r θ * F ρ)
    =
  sumIdx (fun ρ => g M ρ b r θ * F ρ * (if ρ = b then 1 else 0))
```

**insert_delta_right_diag_neg_comm**:
```lean
@[simp] lemma insert_delta_right_diag_neg_comm
    (M r θ : ℝ) (b : Idx) (F : Idx → ℝ) :
  sumIdx (fun ρ => g M ρ b r θ * (-F ρ))
    =
  sumIdx (fun ρ => g M ρ b r θ * (-F ρ) * (if ρ = b then 1 else 0))
```

### 3. Changes to Proofs

- **Line 8940**: Used `insert_delta_right_diag_neg_comm` instead of `insert_delta_right_diag_neg`
- **Line 8957-8958**: Simplified scalar_finish to just `intro ρ; ring`
- **Lines 9041, 9272**: Made g_swap explicit with `rw [g_swap M r θ]`

---

## Error Analysis

### Error Locations

| Line | Error Type | Description |
|------|------------|-------------|
| 8788 | unsolved goals | Outer hb signature |
| 8941 | Type mismatch | After simpa, term doesn't match |
| 8956 | unsolved goals | scalar_finish proof |
| 8999 | simp failed | Nested error |
| 9026 | rewrite failed | Pattern not found |
| 9041 | rewrite failed | g_swap pattern issue |
| 9048 | unsolved goals | Calc block |
| 9077 | unsolved goals | b-branch completion |
| 9228-9323 | Various | Mirror issues in a-branch |
| 9560-9955 | Downstream | Propagated errors |

### Key Issue: Line 8941 Type Mismatch

The error suggests that `insert_delta_right_diag_neg_comm` doesn't produce the right type after simplification. The issue may be:

1. The commuted lemma structure doesn't match what the goal expects
2. The `simpa` tactic is applying too many or wrong simplifications
3. The order of operations in the lemma doesn't align with the goal

---

## Root Cause Analysis

### Hypothesis 1: Lemma Implementation Error

My implementation of the commuted lemmas may not correctly capture the pattern Paul intended. The calc-based proof structure might be introducing unwanted transformations.

### Hypothesis 2: Simplified scalar_finish Too Aggressive

Paul said to remove the case splits and just use `intro ρ; ring`, but this may leave goals unsolved that the case analysis was handling.

### Hypothesis 3: g_swap Application Issues

Making g_swap explicit with `M r θ` arguments may have broken pattern matching elsewhere.

---

## Comparison with Previous State

| Attempt | Error Count | HasDistribNeg? | Notes |
|---------|------------|----------------|-------|
| Previous (13 errors) | 13 | No | Shape mismatches |
| Current (Paul's fixes) | 18 | Unknown | Implementation issues |

**Regression**: 5 additional errors introduced

---

## Recommended Next Steps

### Option A: Revert and Reassess

1. Revert to the 13-error state
2. Re-read Paul's guidance more carefully
3. Implement fixes one at a time with builds between each

### Option B: Debug Current Implementation

1. Focus on line 8941 type mismatch first
2. Check if `insert_delta_right_diag_neg_comm` is correctly structured
3. Try using `exact` or `convert` instead of `simpa`

### Option C: Request Paul's Review

Given the regression, ask Paul to:
1. Verify the lemma implementations are correct
2. Clarify the exact proof tactics to use
3. Provide more specific guidance on the shape adapters

---

## Key Questions for Paul

1. **Lemma Structure**: Is my calc-based proof for the commuted lemmas correct, or should they be more direct?

2. **Application Tactic**: Should I use `simpa using hδ` or a different tactic to apply the commuted lemmas?

3. **scalar_finish Simplification**: Is `intro ρ; ring` sufficient, or do we need more structure?

4. **g_swap Arguments**: Should g_swap take explicit M r θ arguments or be more implicit?

---

## Files Created This Session

1. **`build_paul_shape_fixes_nov11.txt`** - Build log (18 errors)
2. **`DIAGNOSTIC_PAUL_SHAPE_FIXES_REGRESSION_NOV11.md`** - This report

---

## Current State

- ❌ Implementation has more errors than before
- ❌ Shape adapters not working as intended
- ⏸️ **BLOCKED** awaiting clarification on correct implementation

---

**Report Time**: November 11, 2025
**Next**: Need to either debug implementation or get Paul's help on correct lemma structure
**Key Learning**: Shape adapter lemmas require precise syntactic matching - implementation details matter
