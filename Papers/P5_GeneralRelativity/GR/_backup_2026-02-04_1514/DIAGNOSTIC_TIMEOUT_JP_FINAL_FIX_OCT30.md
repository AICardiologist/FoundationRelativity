# Diagnostic: JP's Final Fix - Timeout Issues - October 30, 2025

**Date**: October 30, 2025
**File**: Riemann.lean lines 1700-1786
**Status**: ❌ **BUILD FAILED** - Deterministic timeouts in `payload_split_and_flip`
**Build log**: `build_jp_final_fix_oct30.txt`
**Error count**: 29 errors (increased from 25 baseline)

---

## Executive Summary

JP's corrected drop-in proof for `payload_split_and_flip` was successfully pasted and implemented exactly as provided. However, the build reveals **deterministic timeout errors** at multiple lines in the proof:

- **Line 1768**: `simp` tactic timeout (200000 heartbeats exceeded)
- **Line 1771**: tactic execution timeout
- **Line 1773**: tactic execution timeout
- **Line 1779**: tactic execution timeout
- **Line 1785**: tactic execution timeout (though this line just has `rfl`)

**Root cause**: The `simp`/`simpa` tactics with AC lemmas (`add_assoc`, `add_comm`, `add_left_comm`) are computationally too expensive when working with the large Christoffel symbol and metric derivative expressions after unfolding `f1`, `f2`, `f3`, `f4`.

---

## Errors from Build Log

### Error 1: Line 1768 (First calc step)

```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:1768:12: Tactic `simp` failed with a nested error:
(deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.
```

**Code at line 1768**:
```lean
= sumIdx (fun e => f1 e + f2 e + f3 e + f4 e) := by
    simp [h₀, f1, f2, f3, f4, add_comm, add_left_comm, add_assoc]
```

**Issue**: Unfolding all four definitions (`f1`, `f2`, `f3`, `f4`) plus `h₀`, then applying AC lemmas, creates a huge search space. Each `fᵢ` expands to a large expression involving:
- `dCoord μ (fun r θ => g M ... r θ) r θ`
- `Γtot M r θ ... ... ...`
- Negations and multiplications

### Error 2: Line 1771 (hB rewrite in calc)

```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:1771:12: (deterministic) timeout at `«tactic execution»`, maximum number of heartbeats (200000) has been reached
```

**Code at line 1771**:
```lean
_   = (sumIdx (fun e => f1 e + f2 e)) + sumIdx f3 + sumIdx f4 := by
        simpa [add_assoc] using hB
```

### Error 3: Line 1773 (hC rewrite in calc)

```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:1773:12: (deterministic) timeout at `«tactic execution»`, maximum number of heartbeats (200000) has been reached
```

**Code at line 1773**:
```lean
_   = (sumIdx f1 + sumIdx f2) + sumIdx f3 + sumIdx f4 := by
        simpa using hC
```

### Error 4: Line 1779 (Final reassociation)

```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:1779:12: (deterministic) timeout at `«tactic execution»`, maximum number of heartbeats (200000) has been reached
```

**Code at line 1779**:
```lean
_   =
  (sumIdx f1)
+ (sumIdx f2)
+ (sumIdx f3)
+ (sumIdx f4) := by
        simp [add_assoc, add_comm, add_left_comm]
```

### Error 5: Line 1785 (rfl step)

```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:1785:12: (deterministic) timeout at `«tactic execution»`, maximum number of heartbeats (200000) has been reached
```

**Code at line 1785**:
```lean
_   =
  (sumIdx (fun e => -(dCoord μ (fun r θ => g M e b r θ) r θ) * Γtot M r θ e ν a))
+ (sumIdx (fun e =>  (dCoord ν (fun r θ => g M e b r θ) r θ) * Γtot M r θ e μ a))
+ (sumIdx (fun e => -(dCoord μ (fun r θ => g M a e r θ) r θ) * Γtot M r θ e ν b))
+ (sumIdx (fun e =>  (dCoord ν (fun r θ => g M a e r θ) r θ) * Γtot M r θ e μ b)) := by
        rfl
```

**Note**: This is surprising since it's just `rfl`. May be getting stuck on definitional equality check for the large terms.

---

## Analysis

### Why Timeouts Occur

The proof structure is:

1. **Step h₀**: Flip factors pointwise using `funext e; simp [mul_comm, mul_left_comm, mul_assoc]` ✅ **Succeeds**

2. **Step hA, hB, hC**: Split sums using `simpa [add_assoc] using sumIdx_add_distrib` ⚠️ **Lines 1744, 1751, 1758 succeed with warnings**

3. **Main calc chain**: The issue is here
   - **Line 1768**: Unfolds all 4 definitions and applies AC lemmas → **TIMEOUT**
   - **Lines 1771, 1773**: Uses `simpa` to apply hB, hC → **TIMEOUT**
   - **Line 1779**: Pure AC rearrangement → **TIMEOUT**
   - **Line 1785**: `rfl` on large definitional equality → **TIMEOUT**

### Why the Old Version Didn't Have This Problem

The previous version (with `sumIdx_add3`) failed due to a **type mismatch**, but the tactics themselves didn't timeout because the proof never got far enough to elaborate.

---

## Comparison: What Works vs What Doesn't

### Steps hA, hB, hC (Lines 1740-1758) ✅ SUCCEED (with warnings)

```lean
have hA :
  sumIdx (fun e => f1 e + f2 e + f3 e + f4 e)
    =
    sumIdx (fun e => f1 e + f2 e + f3 e) + sumIdx f4 := by
  simpa [add_assoc] using
    sumIdx_add_distrib (fun e => f1 e + f2 e + f3 e) f4
```

**Why this succeeds**: `f1`, `f2`, `f3`, `f4` are **not expanded** here. They remain as abstract function calls. The `simpa` only needs to rearrange the addition structure, not the full Christoffel expressions.

### Calc chain (Lines 1761-1785) ❌ TIMEOUTS

```lean
calc
  sumIdx (fun e =>
     - Γtot M r θ e ν a * dCoord μ (fun r θ => g M e b r θ) r θ
   +   Γtot M r θ e μ a * dCoord ν (fun r θ => g M e b r θ) r θ
   -   Γtot M r θ e ν b * dCoord μ (fun r θ => g M a e r θ) r θ
   +   Γtot M r θ e μ b * dCoord ν (fun r θ => g M a e r θ) r θ)
      = sumIdx (fun e => f1 e + f2 e + f3 e + f4 e) := by
          simp [h₀, f1, f2, f3, f4, add_comm, add_left_comm, add_assoc]  -- TIMEOUT HERE
```

**Why this times out**: The `simp` unfolds `f1`, `f2`, `f3`, `f4` to their full definitions (each containing Christoffel symbols, metric derivatives, etc.), then tries to:
1. Apply AC lemmas to rearrange the terms
2. Match against the LHS (which has the raw Christoffel expressions)

This creates a massive unification problem.

---

## Possible Solutions

### Option 1: Increase Heartbeat Limit (Quick workaround)

Add at the start of the lemma:
```lean
lemma payload_split_and_flip
    (M r θ : ℝ) (μ ν a b : Idx) :
  ... := by
  set_option maxHeartbeats 1000000
  classical
  ...
```

**Pros**: May allow proof to complete
**Cons**: Doesn't address root cause; may still timeout

### Option 2: Use `rfl` or `trivial` instead of `simp`

If the equalities are definitional, use `rfl` or `trivial`:
```lean
= sumIdx (fun e => f1 e + f2 e + f3 e + f4 e) := rfl  -- or `trivial`
```

### Option 3: Avoid Unfolding - Use Rewrite with hA/hB/hC Directly

Skip the first calc step entirely:
```lean
calc
  sumIdx (fun e => ...)  -- original LHS
    = sumIdx (fun e => f1 e + f2 e + f3 e + f4 e) := by
        rw [h₀]  -- Apply factor flip
        rfl      -- Should be definitional after h₀
    _   = sumIdx (fun e => f1 e + f2 e + f3 e) + sumIdx f4 := hA
    _   = ... -- continue
```

### Option 4: Simpler AC Tactic

Use `ring` instead of `simp` with AC lemmas (if terms are in a ring):
```lean
= sumIdx (fun e => f1 e + f2 e + f3 e + f4 e) := by
    rw [h₀]
    ring
```

But this may not work if `sumIdx` is not fully ring-compatible.

### Option 5: Manual Term Construction

Instead of asking `simp` to figure it out, construct the term manually:
```lean
= sumIdx (fun e => f1 e + f2 e + f3 e + f4 e) := by
    rw [h₀]
    congr
    ext e
    simp only [f1, f2, f3, f4]
    ring
```

---

## Request to JP

Per your guidance:
> "Ping me with the exact error (if any) after this patch; if it still complains about an add‑chain shape, I'll give you a one‑liner simp only reshaper tailored to that goal."

**We need**:

1. A tactic or approach to avoid the timeout at **line 1768** (first calc step)
2. Possibly adjustments to lines 1771, 1773, 1779, 1785 to avoid similar timeouts

**Specific question**: Can we use `rfl` or a lighter tactic instead of `simp [h₀, f1, f2, f3, f4, add_comm, add_left_comm, add_assoc]` at line 1768?

Alternatively, would it help to:
- Apply `h₀` as a rewrite first, then check if the equality is definitional?
- Use `simp only` with a minimal set of lemmas?
- Break the calc chain into smaller `have` statements?

---

## Current Proof Status

**Lemma**: `payload_split_and_flip` (lines 1700-1786)
**Status**: ❌ Proof times out in multiple places
**Build**: ❌ Failed with 29 errors
**Root cause**: `simp`/`simpa` with AC lemmas too expensive for large Christoffel expressions

---

## Files

- **Riemann.lean**: Lines 1700-1786 contain JP's corrected proof (successfully pasted)
- **Build log**: `build_jp_final_fix_oct30.txt`

---

**Prepared by**: Claude Code (Lean 4 Assistant)
**Date**: October 30, 2025
**Status**: Awaiting JP's guidance on timeout mitigation
**Priority**: **HIGH** - Blocking `payload_split_and_flip` compilation
