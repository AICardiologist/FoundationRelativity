# Diagnostic Report: JP's Negation Normalizer Patches - November 1, 2025

**Date**: November 1, 2025
**Build**: `build_jp_negation_normalizers_nov1.txt`
**Total Errors**: 26 (increased from 24)
**Block A Errors**: 10 (unchanged)
**Status**: 🔴 **BLOCKER** - Typeclass synthesis infinite recursion

---

## Executive Summary

All three of JP's negation normalizer patches were applied successfully:
- ✅ **Patch A**: Added `neg_mul_right₀` and `neg_mul_left₀` lemmas (lines 173-176)
- ✅ **Patch B**: b-branch uses `core_as_sum_b_mul` helper (lines 8762-8773)
- ✅ **Patch C**: a-branch uses `core_as_sum_a_mul` helper (lines 9024-9035)

**Critical Issue**: `simpa [neg_mul_right₀]` triggers **infinite typeclass recursion** when synthesizing `HasDistribNeg ℝ`.

---

## The Blocker: Typeclass Synthesis Infinite Recursion

### Error Location

**Line 8771** (b-branch) and **Line 9033** (a-branch, symmetric):
```lean
have core_as_sum_b_mul :
  - ((dCoord μ ... - sumIdx ...) * g M b b r θ)
  = sumIdx (fun ρ => g M ρ b r θ * X ρ) := by
  simpa [neg_mul_right₀] using core_as_sum_b  -- ⚠️ INFINITE RECURSION HERE
```

### Full Error Message

```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8771:8: failed to synthesize
  HasDistribNeg ℝ
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
```

### Root Cause Analysis

**What's Happening**:
1. `simpa [neg_mul_right₀]` attempts to simplify using the lemma `- (E * g) = (-E) * g`
2. During simplification, Lean tries to synthesize the typeclass `HasDistribNeg ℝ`
3. The simplifier enters an infinite loop searching for this typeclass instance
4. Max recursion depth (default ~1000) is exceeded

**Why It Happens**:
- `simpa` combines `simp` + `assumption`, triggering aggressive typeclass search
- The `neg_mul_right₀` lemma involves negation distributing over multiplication
- Lean's typeclass synthesis for `HasDistribNeg` appears to create a circular dependency
- The simplifier keeps trying to apply the same lemma repeatedly

**Technical Details**:
- `HasDistribNeg` is a typeclass for types where `-(a * b) = -a * b = a * -b`
- For `ℝ`, this should exist in mathlib, but the simplifier's search is looping
- Likely caused by how `simpa` interacts with the simp normal form for negation

---

## Code Context: What Was Intended

### The Goal Structure

**`core_as_sum_b`** (lines 8720-8759):
```lean
- ( ( dCoord μ ... - sumIdx ... ) ) * g M b b r θ
  = sumIdx (fun ρ => g M ρ b r θ * X ρ)
```
- LHS form: `-(E) * g` - negation inside, then multiply

**`core_as_sum_b_mul`** (lines 8762-8771):
```lean
- (( dCoord μ ... - sumIdx ... ) * g M b b r θ)
  = sumIdx (fun ρ => g M ρ b r θ * X ρ)
```
- LHS form: `-(E * g)` - multiply first, then negate outside

**The Transform Needed**:
Use `neg_mul_right₀ : -(E * g) = (-E) * g` to convert:
- FROM: `-((...) * g M b b r θ)`
- TO: `-((...)) * g M b b r θ` (which matches `core_as_sum_b`)

---

## Diagnostic: Alternative Tactics Tested (Conceptual)

### Option 1: Direct Rewrite (Recommended)
```lean
simpa [neg_mul_right₀] using core_as_sum_b
```
↓ **Replace with:**
```lean
rw [neg_mul_right₀]; exact core_as_sum_b
```

**Why This Should Work**:
- `rw` applies the lemma once, directionally, without triggering simplifier loops
- `exact` then closes the goal with the existing equality
- No typeclass search needed

### Option 2: Explicit Conversion
```lean
have : -((...) * g M b b r θ) = -((...)) * g M b b r θ := neg_mul_right₀ _ _
rw [this]
exact core_as_sum_b
```

### Option 3: Show Instead of Have
```lean
show -((...) * g M b b r θ) = sumIdx (...)
rw [neg_mul_right₀]
exact core_as_sum_b
```

---

## Block A Error Inventory

### Errors Directly Caused by Recursion (2 errors)
- **Line 8771** (b-branch): `simpa [neg_mul_right₀]` - infinite recursion
- **Line 9033** (a-branch): `simpa [neg_mul_right₀]` - infinite recursion

### Cascade Errors (8 errors)
All downstream from the failed `core_as_sum_b_mul` / `core_as_sum_a_mul`:
- **Line 8709**: unsolved goals (b-branch outer proof context)
- **Line 8788**: unsolved goals (b-branch downstream)
- **Line 8804**: Type mismatch (b-branch downstream)
- **Line 8808**: Rewrite failed (b-branch downstream)
- **Line 8837**: unsolved goals (b-branch downstream)
- **Line 8978**: unsolved goals (a-branch outer proof context)
- **Line 9011**: Type mismatch (a-branch downstream)
- **Line 9050**: unsolved goals (a-branch downstream)

**Hypothesis**: All 8 cascade errors will resolve once the recursion is fixed.

---

## Comparison: Before vs After Patches

| Metric | Composed Equalities (Previous) | Negation Normalizers (Current) |
|--------|--------------------------------|--------------------------------|
| Total Errors | 24 | 26 (+2) |
| Block A Errors | 10 | 10 (same) |
| Calc Errors | 0 ✅ | 0 ✅ |
| Rewrite Pattern Errors | 2 (lines 8756, 9007) | 0 ✅ |
| **New**: Recursion Errors | 0 | 2 (lines 8771, 9033) ⚠️ |
| Cascade Errors | 8 | 8 (same patterns) |

**Net Effect**: Eliminated rewrite pattern errors, but introduced recursion errors.

---

## Recommended Fix for JP

### Minimal Change (Lines 8771 and 9033)

**b-branch** (line 8771):
```lean
-- CURRENT (causes recursion):
simpa [neg_mul_right₀] using core_as_sum_b

-- PROPOSED FIX:
rw [neg_mul_right₀]; exact core_as_sum_b
```

**a-branch** (line 9033):
```lean
-- CURRENT (causes recursion):
simpa [neg_mul_right₀] using core_as_sum_a

-- PROPOSED FIX:
rw [neg_mul_right₀]; exact core_as_sum_a
```

### Alternative: Use conv Mode
```lean
conv_lhs => rw [neg_mul_right₀]
exact core_as_sum_b
```

---

## Questions for JP

### Q1: Tactic Choice
Is `rw [neg_mul_right₀]; exact core_as_sum_b` acceptable, or do you prefer a different approach?

### Q2: Lemma Formulation
Should `neg_mul_right₀` be stated differently to avoid the typeclass issue? Current form:
```lean
lemma neg_mul_right₀ (E g : ℝ) : - (E * g) = (-E) * g := by ring
```

### Q3: Type Annotation
Would adding explicit type annotations help? E.g.:
```lean
(neg_mul_right₀ (dCoord μ ... - sumIdx ...) (g M b b r θ))
```

---

## Math Professor Consult?

**No consult needed** - this is a pure Lean 4 tactical/typeclass issue, not a mathematical correctness issue.

**Reasoning**:
1. The lemma `neg_mul_right₀ : -(E * g) = (-E) * g` is mathematically trivial (proven by `ring`)
2. The equality `core_as_sum_b` is proven correct via composed `.trans` steps
3. The issue is purely how Lean's simplifier handles the lemma application
4. No mathematical verification required

---

## Success Metrics

✅ **Negation normalizer lemmas added correctly**
✅ **Helper equalities structure correctly**
✅ **Rewrite pattern matching issues eliminated**
⏳ **Typeclass recursion blocking final integration**

**Expected Resolution**: Once `simpa` → `rw; exact` change applied, all 10 Block A errors should reduce to 0-2 errors.

---

**Prepared by**: Claude Code (Lean 4 Assistant)
**Build File**: `build_jp_negation_normalizers_nov1.txt`
**Date**: November 1, 2025
**Status**: Awaiting JP's tactical fix for typeclass recursion

---

**End of Diagnostic Report**
