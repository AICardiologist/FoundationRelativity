# DIAGNOSTIC: Calc Chain Errors in Paul's Outer-Sum δ-Pattern

**Date**: November 7, 2025
**Status**: 🔴 **Calc chain steps failing - need debugging**

---

## Error Summary

**Total errors**: 19 (baseline was 18, so **+1 error**)

**Breakdown**:
- **2 errors** in `hb_plus` calc chain (lines 8778, 8790)
- **2 errors** in `ha_plus` calc chain (lines 9031, 9044)
- **15 errors** in baseline code (old `hb`/`ha` + downstream)

**Key Finding**: Pattern structure is correct but **δ-collapse step fails**

---

## Calc Chain Error Details

### Error 1: Line 8778 (`hb_plus` - final calc step)

**Location**: Riemann.lean:8778:59

**Code**:
```lean
_   = (- RiemannUp M r θ b a μ ν) * g M b b r θ := by
        simp [mul_assoc, sumIdx_delta_right]  -- ← FAILS HERE
```

**Previous step** (line 8775-8777):
```lean
_   = sumIdx (fun ρ =>
        (- RiemannUp M r θ ρ a μ ν) * g M ρ b r θ * (if ρ = b then 1 else 0)) := by
        simpa using insert_delta_right_diag_neg M r θ b (fun ρ => RiemannUp M r θ ρ a μ ν)
```

**Expected behavior**: `simp [mul_assoc, sumIdx_delta_right]` should:
1. Apply `sumIdx_delta_right` to collapse the Kronecker delta
2. Result: `sumIdx (fun ρ => A ρ * (if ρ = b then 1 else 0)) = A b`

**Actual behavior**: Unsolved goals (context is too long to show goal)

**Diagnosis**: The `simp` tactic isn't applying `sumIdx_delta_right`. Possible causes:
1. Pattern mismatch - maybe `sumIdx_delta_right` expects different argument order
2. Need to unfold something first
3. `mul_assoc` causing issues by rearranging before collapse
4. Type mismatch in the function

---

### Error 2: Line 8790 (`hb_plus` - sorry placeholder)

**Code**:
```lean
rw [h_rhs_transform]
sorry  -- LHS = RHS algebra (no more nested sums!)
```

**Status**: This is expected - it's our placeholder for the final algebra

---

### Errors 3-4: Lines 9031, 9044 (`ha_plus` calc chain)

**Status**: Symmetric to errors 1-2 in `hb_plus`

---

## What's Working

✅ **NO TIMEOUTS** - major success!
✅ Steps 1-3 of calc chain compile:
- Negation distribution works
- Product commutation with `ring` works
- δ-insertion with `insert_delta_right_diag_neg` works

❌ Step 4 (δ-collapse) fails

---

## Diagnostic Questions

### Q1: Is `sumIdx_delta_right` the right lemma?

**Signature** (from line 1718):
```lean
@[simp] lemma sumIdx_delta_right (A : Idx → ℝ) (b : Idx) :
  sumIdx (fun ρ => A ρ * (if ρ = b then 1 else 0)) = A b
```

**Our term**:
```lean
sumIdx (fun ρ => (- RiemannUp M r θ ρ a μ ν) * g M ρ b r θ * (if ρ = b then 1 else 0))
```

**Issue**: Our term has TWO multiplications before the delta:
- `A ρ` in lemma = `(- RiemannUp M r θ ρ a μ ν) * g M ρ b r θ` in our term
- The lemma expects `A ρ * delta`, but we have `(term1 * term2) * delta`

**Hypothesis**: `mul_assoc` should reassociate to `term1 * (term2 * delta)`, but maybe it's not working?

### Q2: Should we apply lemma directly instead of via `simp`?

**Alternative**:
```lean
_   = (- RiemannUp M r θ b a μ ν) * g M b b r θ := by
        exact sumIdx_delta_right (fun ρ => (- RiemannUp M r θ ρ a μ ν) * g M ρ b r θ) b
```

### Q3: Do we need to massage the term first?

**Alternative**:
```lean
_   = (- RiemannUp M r θ b a μ ν) * g M b b r θ := by
        rw [sumIdx_delta_right]
        rfl
```

---

## Proposed Fixes

### Fix 1: Use `exact` with explicit lemma application

Replace:
```lean
simp [mul_assoc, sumIdx_delta_right]
```

With:
```lean
exact sumIdx_delta_right (fun ρ => (- RiemannUp M r θ ρ a μ ν) * g M ρ b r θ) b
```

### Fix 2: Manual reassociation

```lean
_   = (- RiemannUp M r θ b a μ ν) * g M b b r θ := by
        have : sumIdx (fun ρ => ((- RiemannUp M r θ ρ a μ ν) * g M ρ b r θ) * (if ρ = b then 1 else 0))
             = (- RiemannUp M r θ b a μ ν) * g M b b r θ := by
          rw [sumIdx_delta_right]
        exact this
```

### Fix 3: Step-by-step with `conv`

```lean
_   = (- RiemannUp M r θ b a μ ν) * g M b b r θ := by
        conv_lhs => rw [sumIdx_delta_right]
```

---

## Next Steps

1. **Test Fix 1** (most direct) - replace `simp` with `exact`
2. If that fails, **examine goal state** to see what Lean actually has
3. **Test Fix 2** or **Fix 3** as fallback
4. Apply same fix to `ha_plus` (line 9031)

---

## Impact on Error Count

**Current**: 19 errors
**If calc chains fixed**: 17 errors (19 - 2 `sorry` placeholders)
**Baseline**: 18 errors

**Goal**: Get to ≤17 errors (below baseline) by fixing calc chains

---

**Files**:
- Main: `Riemann.lean:8778, 9031`
- Build log: `build_paul_outer_delta_cleanup_nov7.txt`
