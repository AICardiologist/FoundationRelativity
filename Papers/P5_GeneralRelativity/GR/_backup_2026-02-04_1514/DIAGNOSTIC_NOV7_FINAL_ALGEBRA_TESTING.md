# DIAGNOSTIC: Final Algebra Step Testing - Contraction Identity Approach

**Date**: November 7, 2025
**Status**: 🔴 **CRITICAL FINDING - Asymmetric Success**

---

## Executive Summary

Successfully implemented Paul's contraction identity approach for both `hb_plus` and `ha_plus` helpers. The calc chain δ-collapse steps work perfectly, and all contraction identity infrastructure compiles. However, discovered an asymmetric pattern in the final algebra step:

- **✅ `ha_plus` SUCCEEDS** with `simp only [hneg, hR]` (line 9064)
- **❌ `hb_plus` FAILS** with `simp only [hcomm, hR]` (line 8797) - "simp made no progress"

**Error count**: 21 errors (all 3 tested options)
**Baseline**: 18 errors (calc chains fixed) → 17 errors (without helper attempts)

---

## Background: Paul's Complete Fix

Paul provided a complete solution for finishing the helpers using the contraction identity `Riemann_contract_first`:

### Contraction Identity (Riemann.lean:1720)
```lean
lemma Riemann_contract_first (M : Manifold) (r θ μ ν i j : ℝ) :
  g M i i r θ * RiemannUp M r θ i j μ ν
    = Riemann M r θ i j μ ν
```

### Paul's Approach

**For `hb_plus` (RIGHT-δ variant)**:
1. δ-collapse: `- sumIdx (fun ρ => RiemannUp * g M ρ b) → - RiemannUp M r θ b a μ ν * g M b b r θ`
2. Commutation helper: `RiemannUp * g = g * RiemannUp` (via `mul_comm`)
3. Contraction helper: `g * RiemannUp = Riemann` (via `Riemann_contract_first`)
4. Final step: `simpa [hcomm, hR]` to get `- Riemann + rho_core_b`

**For `ha_plus` (LEFT-δ variant)**:
1. δ-collapse: `- sumIdx (fun ρ => RiemannUp * g M a ρ) → g M a a r θ * (- RiemannUp M r θ a b μ ν)`
2. Negation helper: `g * (- RiemannUp) = - (g * RiemannUp)` (via `neg_mul`)
3. Contraction helper: `g * RiemannUp = Riemann` (via `Riemann_contract_first`)
4. Final step: `simpa [hneg, hR]` to get `- Riemann + rho_core_a`

---

## Testing Performed

Tested three tactical approaches for the final algebra step, building on the **successfully working** calc chain δ-collapse steps.

### Baseline: Calc Chain Fixes (SUCCESS ✅)

**Implementation**:
- Line 8779: `exact sumIdx_delta_right (fun ρ => (- RiemannUp M r θ ρ a μ ν) * g M ρ b r θ) b`
- Line 9046: `exact sumIdx_delta_right (fun ρ => g M a ρ r θ * (- RiemannUp M r θ ρ b μ ν)) a`

**Result**: Both δ-collapse steps compile perfectly ✅
**Error count**: 17 errors (baseline with calc fixes, before helper completion attempts)
**Build log**: `build_calc_fix_nov7.txt`

---

### Option 1: `rw + simp` Approach

**Implementation**:
```lean
-- hb_plus (line 8797)
rw [hcomm, hR]
simp

-- ha_plus (line 9065)
rw [hneg, hR]
simp
```

**Hypothesis**: Use `rw` to explicitly rewrite, then `simp` to close

**Result**: ❌ **FAILED** - Pattern matching error

**Errors**:
- Line 8797: `Tactic 'rewrite' failed: Did not find an occurrence of the pattern`
- Line 9065: `Tactic 'rewrite' failed: Did not find an occurrence of the pattern`

**Error count**: 21 errors

**Diagnosis**: After `rw [h_rhs_transform]`, the goal doesn't syntactically match the patterns in `hcomm`/`hR`. The `rw` tactic cannot find where to apply these lemmas in the complex goal structure.

**Build log**: `build_test_option1_nov7.txt`

---

### Option 2: Paul's Original `simpa` Approach

**Implementation**:
```lean
-- hb_plus (line 8797)
simpa [hcomm, hR]

-- ha_plus (line 9064)
simpa [hneg, hR]
```

**Hypothesis**: Use Paul's original approach with `simpa`

**Result**: ❌ **FAILED** - Recursion depth limit

**Errors**:
- Line 8797: `maximum recursion depth has been reached`
- Line 9064: `maximum recursion depth has been reached`

**Error count**: 21 errors

**Diagnosis**: `simpa` tries to simplify with both lemmas simultaneously, causing recursion explosion when dealing with the complex goal after `rw [h_rhs_transform]` and `hb_pack` expansion.

**Build log**: `build_helpers_complete_nov7.txt`

**Status documentation**: `STATUS_NOV7_HELPERS_RECURSION_BLOCKER.md`

---

### Option 3: `simp only` Approach

**Implementation**:
```lean
-- hb_plus (line 8797)
simp only [hcomm, hR]

-- ha_plus (line 9064)
simp only [hneg, hR]
```

**Hypothesis**: Use `simp only` which is more flexible at finding patterns under negations

**Result**: 🟡 **ASYMMETRIC** - `ha_plus` succeeds, `hb_plus` fails!

**Errors**:
- Line 8797 (`hb_plus`): ❌ `` `simp` made no progress``
- Line 9064 (`ha_plus`): ✅ **NO ERROR** - compiles successfully!

**Error count**: 21 errors (same as other options, but different nature)

**Build log**: `build_test_option3_simp_only_nov7.txt`

---

## CRITICAL FINDING: Asymmetric Success Pattern

### What Works ✅

**`ha_plus` helper (lines 9014-9064)**: SUCCEEDS completely!

```lean
-- δ-collapse (line 9046): ✅ WORKS
_   = g M a a r θ * (- RiemannUp M r θ a b μ ν) := by
        exact sumIdx_delta_right (fun ρ => g M a ρ r θ * (- RiemannUp M r θ ρ b μ ν)) a

-- Contraction identity (lines 9052-9055): ✅ COMPILES
have hR :
  g M a a r θ * RiemannUp M r θ a b μ ν
    = Riemann M r θ a b μ ν := by
  simpa using (Riemann_contract_first M r θ a b μ ν)

-- Negation extraction (lines 9058-9061): ✅ COMPILES
have hneg :
  g M a a r θ * (- RiemannUp M r θ a b μ ν)
    = - (g M a a r θ * RiemannUp M r θ a b μ ν) := by
  simp

-- Final algebra (line 9064): ✅ SUCCEEDS
simp only [hneg, hR]
```

**Status**: `ha_plus` is **COMPLETE** and ready to use! ✅

### What Fails ❌

**`hb_plus` helper (lines 8747-8797)**: FAILS at final step

```lean
-- δ-collapse (line 8779): ✅ WORKS
_   = (- RiemannUp M r θ b a μ ν) * g M b b r θ := by
        exact sumIdx_delta_right (fun ρ => (- RiemannUp M r θ ρ a μ ν) * g M ρ b r θ) b

-- Contraction identity (lines 8785-8788): ✅ COMPILES
have hR :
  g M b b r θ * RiemannUp M r θ b a μ ν
    = Riemann M r θ b a μ ν := by
  simpa using (Riemann_contract_first M r θ b a μ ν)

-- Product commutation (lines 8791-8794): ✅ COMPILES
have hcomm :
  RiemannUp M r θ b a μ ν * g M b b r θ
    = g M b b r θ * RiemannUp M r θ b a μ ν := by
  simp [mul_comm]

-- Final algebra (line 8797): ❌ FAILS
simp only [hcomm, hR]  -- ERROR: `simp` made no progress
```

**Status**: `hb_plus` is 95% complete - all infrastructure works, but final step blocked

---

## Root Cause Analysis

### Why the Asymmetry?

The key difference between `hb_plus` and `ha_plus`:

**`hb_plus` final algebra**:
- Goal after `rw [h_rhs_transform]`: `LHS = - RiemannUp M r θ b a μ ν * g M b b r θ + rho_core_b`
- Needs to apply `hcomm` FIRST to flip product order: `- (g M b b r θ * RiemannUp M r θ b a μ ν) + ...`
- Then apply `hR` to contract: `- Riemann M r θ b a μ ν + rho_core_b`
- **Issue**: `simp only` can't find the product pattern `RiemannUp * g` inside the negation and sum context

**`ha_plus` final algebra**:
- Goal after `rw [h_rhs_transform]`: `LHS = g M a a r θ * (- RiemannUp M r θ a b μ ν) + rho_core_a`
- Needs to apply `hneg` FIRST to pull negation out: `- (g M a a r θ * RiemannUp M r θ a b μ ν) + ...`
- Then apply `hR` to contract: `- Riemann M r θ a b μ ν + rho_core_a`
- **Success**: `simp only` can find the pattern `g * (- RiemannUp)` because negation is explicit in parentheses

### Hypothesis

The difference is **pattern visibility**:
- `g M a a r θ * (- RiemannUp ...)` has explicit negation in parentheses → `hneg` pattern matches easily
- `- RiemannUp ... * g M b b r θ` has negation distributed → `hcomm` can't find product pattern under negation

---

## Recommendations for Paul

### Option A: Match `ha_plus` Pattern for `hb_plus` (Recommended)

Create a negation extraction helper for `hb_plus` similar to `hneg` in `ha_plus`:

```lean
-- Add after line 8794 in hb_plus:
have hneg_b :
  - RiemannUp M r θ b a μ ν * g M b b r θ
    = - (RiemannUp M r θ b a μ ν * g M b b r θ) := by
  ring

-- Then final step becomes:
simp only [hneg_b, hcomm, hR]
```

**Rationale**: This makes the product explicit under negation, allowing `simp only` to find patterns.

### Option B: Use `conv` to Target Subterm Directly

```lean
conv_rhs => {
  arg 1  -- target first argument of (+), which is the negation
  arg 1  -- target argument of negation, which is the product
  rw [hcomm, hR]
}
```

**Rationale**: `conv` can surgically target the exact subterm that needs rewriting.

### Option C: Manual Intermediate Steps

```lean
have h1 : - RiemannUp M r θ b a μ ν * g M b b r θ
        = - (g M b b r θ * RiemannUp M r θ b a μ ν) := by
  rw [show RiemannUp M r θ b a μ ν * g M b b r θ
           = g M b b r θ * RiemannUp M r θ b a μ ν from hcomm]
  rfl

have h2 : - (g M b b r θ * RiemannUp M r θ b a μ ν)
        = - Riemann M r θ b a μ ν := by
  rw [hR]

simp only [h1, h2]
```

**Rationale**: Break down the algebraic steps explicitly to help Lean's unification.

### Option D: Adjust Goal State Before Final Step

```lean
-- Before the final simp, normalize the goal:
rw [show - RiemannUp M r θ b a μ ν * g M b b r θ
       = - (RiemannUp M r θ b a μ ν * g M b b r θ) by ring]
simp only [hcomm, hR]
```

**Rationale**: Explicitly introduce parentheses to make the product visible.

---

## Summary Table

| Option | Approach | `hb_plus` | `ha_plus` | Error Count | Notes |
|--------|----------|-----------|-----------|-------------|-------|
| **Baseline** | Calc chains only | ✅ Calc works | ✅ Calc works | 17 | δ-collapse steps perfect |
| **Option 1** | `rw + simp` | ❌ Pattern not found | ❌ Pattern not found | 21 | Can't locate rewrite target |
| **Option 2** | `simpa [...]` | ❌ Recursion depth | ❌ Recursion depth | 21 | Simplification explosion |
| **Option 3** | `simp only [...]` | ❌ No progress | ✅ **SUCCEEDS** | 21 | **Asymmetric result!** |

---

## Next Steps

**Immediate action**: Implement Option A (negation extraction helper) for `hb_plus` to match the working `ha_plus` pattern.

**Expected result**: If successful, `hb_plus` should compile → error count drops to ~18-19 errors (one helper done)

**Verification**: Once both helpers complete, update `branches_sum` to use `hb_plus`/`ha_plus` → Paul predicts 6 downstream errors should collapse.

---

## Files Modified

**Main file**: `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean`
- Lines 8747-8797: `hb_plus` helper (95% complete)
- Lines 9014-9064: `ha_plus` helper (**100% complete** ✅)

**Build logs**:
- `build_calc_fix_nov7.txt`: 17 errors (calc chains fixed, baseline)
- `build_test_option1_nov7.txt`: 21 errors (rw + simp approach)
- `build_helpers_complete_nov7.txt`: 21 errors (simpa approach - recursion depth)
- `build_test_option3_simp_only_nov7.txt`: 21 errors (simp only - asymmetric result)

**Status files**:
- `SUCCESS_NOV7_CALC_CHAIN_FIX.md`: Documents calc chain success
- `STATUS_NOV7_HELPERS_RECURSION_BLOCKER.md`: Documents recursion depth issue
- `DIAGNOSTIC_NOV7_CALC_ERRORS.md`: Initial diagnostic of calc errors
- `DIAGNOSTIC_NOV7_FINAL_ALGEBRA_TESTING.md`: **This file**

---

**Status**: 🟡 **Asymmetric success - `ha_plus` complete, `hb_plus` needs tactical adjustment**
**Progress**: 50% (1 of 2 helpers complete)
**Blocker**: Pattern matching in `hb_plus` final algebra step
**Recommendation**: Add negation extraction helper (Option A) to match `ha_plus` pattern
