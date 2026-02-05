# ESCALATION TO PAUL: Recursion Error in Fix #1 - November 12, 2024

**Status**: ❌ **BLOCKER - Fix Introduced Recursion Errors**
**Error Count**: 21 errors (was 18 baseline) - **DEGRADED by 3**
**For**: Paul
**From**: Claude Code
**Severity**: CRITICAL - First fix cannot proceed due to tactic recursion

---

## Executive Summary

Applied your exact surgical fix for line 8986 (first b-branch error), but the `simpa` tactic at line 8990 enters **maximum recursion depth**, introducing 3 new errors:

1. **Line 8990**: `maximum recursion depth has been reached` in `simpa [hs, neg_mul, mul_neg, mul_comm, mul_left_comm, mul_assoc]`
2. **Line 8993**: Type mismatch - `hδ` has wrong type (cascading from 8990 failure)
3. **Line 9008**: Outer proof `h_insert_delta_for_b` fails with "unsolved goals" (cascading)

**Request**: Revised tactic for line 8990 that avoids the recursion loop.

---

## Exact Code Applied (Your Fix)

Replaced lines 8984-8986 with lines 8984-8993:

```lean
      -- The goal's LHS is `sumIdx (fun ρ => g M ρ b r θ * -(G ρ))` (definitional after `set`).
      -- Swap metric indices inside the integrand (C), then insert δ (A) and collapse.
      have hswap_fun :
          (fun ρ => -(g M b ρ r θ * G ρ)) = (fun ρ => g M ρ b r θ * -(G ρ)) := by
        funext ρ
        have hs : g M b ρ r θ = g M ρ b r θ := g_swap_local M r θ b ρ
        -- push the minus sign to the right factor and swap indices using the shim wrappers
        simpa [hs, neg_mul, mul_neg, mul_comm, mul_left_comm, mul_assoc]  -- ❌ RECURSION HERE
      have hδ := insert_delta_right_of_commuted_neg M r θ b G
      -- Collapse the δ with the standard right-δ eliminator.
      simpa [hswap_fun, sumIdx_delta_right] using hδ  -- ❌ TYPE MISMATCH (cascading)
```

Location: Riemann.lean:8985-8993

---

## Error Details

### Error #1: Maximum Recursion Depth (Line 8990)

```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8990:8: Tactic `simp` failed with a nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
```

**Problematic tactic**:
```lean
simpa [hs, neg_mul, mul_neg, mul_comm, mul_left_comm, mul_assoc]
```

**Root cause**: The combination of `mul_comm`, `mul_left_comm`, and `mul_assoc` creates an infinite rewrite loop. The simplifier keeps applying these commutativity/associativity lemmas in cycles.

---

### Error #2: Type Mismatch (Line 8993)

```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8993:6: Type mismatch: After simplification, term
  hδ
 has type
  (sumIdx fun k => -G k * g M k b r θ) = sumIdx fun ρ => if ρ = b then -(g M b ρ r θ * G ρ) else 0
but is expected to have type
  (sumIdx fun ρ =>
      -(g M b ρ r θ *
          ((dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ - dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ -
              sumIdx fun ρ_1 => Γtot M r θ ρ_1 μ a * Γtot M r θ ρ ν ρ_1) +
            sumIdx fun ρ_1 => Γtot M r θ ρ_1 ν a * Γtot M r θ ρ μ ρ_1))) =
    sumIdx fun ρ =>
      if ρ = b then
        -(g M b ρ r θ *
            ((dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ - dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ -
                sumIdx fun ρ_1 => Γtot M r θ ρ_1 μ a * Γtot M r θ ρ ν ρ_1) +
              sumIdx fun ρ_1 => Γtot M r θ ρ_1 ν a * Γtot M r θ ρ μ ρ_1))
      else 0
```

**Analysis**: Because line 8990 fails, `hswap_fun` is not proven. The `simpa` at line 8993 cannot simplify properly, and `hδ` has type with `G k` instead of the expanded definition.

---

### Error #3: Unsolved Goals (Line 9008)

```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9008:33: unsolved goals
```

**Context**: This is the outer proof `h_insert_delta_for_b` which depends on the fix at 8985-8993. Since that fix fails, the outer proof fails with unsolved goals.

---

## Context: What the Goal Is

At line 8985, after the `set G` definition (lines 8975-8980), the goal's LHS is:

```lean
sumIdx (fun ρ => -(g M b ρ r θ * G ρ))
```

Your pattern (C → A → collapse) aims to:
1. **C (swap)**: Rewrite to `sumIdx (fun ρ => g M ρ b r θ * -(G ρ))`
2. **A (δ-insertion)**: Apply `insert_delta_right_of_commuted_neg` to insert Kronecker delta
3. **Collapse**: Eliminate the sum with `sumIdx_delta_right`

The issue is in **step C (line 8990)**: the pointwise proof needs to show:
```lean
-(g M b ρ r θ * G ρ) = g M ρ b r θ * -(G ρ)
```

---

## Why the Recursion Occurs

The `simpa` tactic with these lemmas:
```lean
[hs, neg_mul, mul_neg, mul_comm, mul_left_comm, mul_assoc]
```

Creates rewrite cycles:
- `mul_comm` swaps `A * B` → `B * A`
- `mul_left_comm` moves factors: `A * (B * C)` → `B * (A * C)`
- `mul_assoc` changes grouping

Lean's simplifier doesn't have a canonical form for multiplication with mixed negations, so it keeps trying different orderings infinitely.

---

## Possible Solutions (Request)

### Option 1: Explicit Rewrite Sequence (Recommended)
Replace the recursive `simpa` at line 8990 with deterministic `rw` steps:

```lean
      have hswap_fun :
          (fun ρ => -(g M b ρ r θ * G ρ)) = (fun ρ => g M ρ b r θ * -(G ρ)) := by
        funext ρ
        have hs : g M b ρ r θ = g M ρ b r θ := g_swap_local M r θ b ρ
        rw [neg_mul, hs, mul_neg]  -- Deterministic 3-step rewrite
```

### Option 2: simp only with Specific Lemmas
Use `simp only` instead of `simpa` to avoid non-termination:

```lean
      have hswap_fun :
          (fun ρ => -(g M b ρ r θ * G ρ)) = (fun ρ => g M ρ b r θ * -(G ρ)) := by
        funext ρ
        have hs : g M b ρ r θ = g M ρ b r θ := g_swap_local M r θ b ρ
        simp only [neg_mul, hs, mul_neg]
```

### Option 3: ring_nf + rw
Use `ring_nf` to normalize then rewrite:

```lean
      have hswap_fun :
          (fun ρ => -(g M b ρ r θ * G ρ)) = (fun ρ => g M ρ b r θ * -(G ρ)) := by
        funext ρ
        have hs : g M b ρ r θ = g M ρ b r θ := g_swap_local M r θ b ρ
        ring_nf
        rw [hs]
```

---

## Similar Issue at Line 8993?

The second `simpa` at line 8993 may also need revision:

```lean
simpa [hswap_fun, sumIdx_delta_right] using hδ
```

**Potential issue**: If `G` is not expanding properly, this may also fail. Consider:

```lean
rw [← hswap_fun]
exact hδ  -- Or: apply hδ
```

---

## Comparison: Before vs After

| Metric | Baseline | After Paul's Fix |
|--------|----------|------------------|
| **Error Count** | 18 errors | 21 errors ❌ |
| **Line 8986** | Type mismatch | Recursion error ❌ |
| **Line 8993** | N/A | Type mismatch ❌ |
| **Line 9008** | N/A | Unsolved goals ❌ |

---

## Files Created

- **ESCALATION_TO_PAUL_RECURSION_ERROR_NOV12.md** - This report
- **build_paul_fix1_applied_nov12.txt** - Full build log showing 21 errors

---

## Request Summary

**Problem**: Your surgical fix line 8990 hits max recursion depth with `simpa [hs, neg_mul, mul_neg, mul_comm, mul_left_comm, mul_assoc]`

**Request**: Provide revised tactic for line 8990 (and possibly 8993) that avoids recursion, using one of:
- Explicit `rw` sequence
- `simp only` with minimal lemmas
- `ring_nf` + `rw`

**Format**: Please provide the exact replacement code for lines 8985-8993 with the revised tactic.

---

## Current State

- **File**: Riemann.lean with your fix applied (21 errors)
- **Blocker**: Cannot proceed with Bucket 1 fixes until this is resolved
- **Status**: Awaiting your revised tactic for line 8990

---

**Report Time**: November 12, 2024
**Key Finding**: `simpa` with commutativity lemmas causes infinite recursion
**Blocker**: Line 8990 tactic needs revision before proceeding with remaining 17 b-branch errors

---

## Build Evidence

Full error log available at: `Papers/P5_GeneralRelativity/GR/build_paul_fix1_applied_nov12.txt`

Error lines extracted:
```
2244: error: Riemann.lean:8990:8: maximum recursion depth
2248: error: Riemann.lean:8993:6: Type mismatch
2265: error: Riemann.lean:9008:33: unsolved goals
```

Plus 18 other pre-existing errors from baseline.
