# Paul's Surgical Fixes Implementation Plan - November 9, 2025

**Status**: ⏸ IN PROGRESS - Heartbeat fences applied, need to continue
**File**: `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean`

---

## Executive Summary

Following Paul's guidance, I'm implementing surgical, shape-preserving fixes for the 8-error baseline:
- **Step 2 COMPLETE**: Added local heartbeat fences at 3 slow spots (8819, 8870)
- **Step 3 PENDING**: Need to apply Paul's surgical micro-fixes for 5 non-timeout errors

---

## Step 2: Heartbeat Fences ✅ APPLIED (2 of 3)

### Fence 1: h_pack (Line 8819) ✅ COMPLETE

**Location**: `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean:8819`

**Applied**:
```lean
-- canonical packers for finite sums
set_option maxHeartbeats 700000 in
simp [sub_eq_add_neg, sumIdx_add_distrib, sumIdx_map_sub,
      add_comm, add_left_comm, add_assoc]
```

### Fence 2: h_delta (Line 8870) ✅ COMPLETE

**Location**: `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean:8870`

**Applied**:
```lean
-- Pack with the (already correct) −Σ ρ (RiemannUp⋅g) part
set_option maxHeartbeats 700000 in
simpa [sumIdx_add_distrib, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
       h_core]
```

### Fence 3: hb proof (Line ~9102) ⏸ PENDING

**Location**: Need to find the exact location where the hb proof has a timeout

Paul's guidance says this is "the final hb stitching" - likely in the large calc block that assembles the hb proof. The hb proof starts at line 8892 and ends around line 9102.

**To apply**: Add `set_option maxHeartbeats 700000 in` before the slow calc or simpa statement in the hb proof.

---

## Step 3: Surgical Micro-Fixes ⏸ PENDING

Paul provided specific fixes for the 5 non-timeout errors. These are shape-preserving and won't change h_pack/h_congr/h_delta architecture.

### Fix A: Line 9650 - h_cancel Type Mismatch

**Problem**: `h_cancel` has the correct content but wrong bracketing/ordering of the four sumIdx blocks.

**Paul's Fix**:
```lean
-- Put the LHS into the bracketing that `h_cancel` was written for
have h_cancel' :
  (((sumIdx (fun ρ => -Γtot M r θ ρ ν a * dCoord μ (fun r θ => g M ρ b r θ) r θ
                     + Γtot M r θ ρ μ a * dCoord ν (fun r θ => g M ρ b r θ) r θ))
    +  sumIdx (fun ρ => -Γtot M r θ ρ μ a * dCoord ν (fun r θ => g M ρ b r θ) r θ
                     + Γtot M r θ ρ ν a * dCoord μ (fun r θ => g M ρ b r θ) r θ)))
   + ((sumIdx (fun ρ => -Γtot M r θ ρ ν b * dCoord μ (fun r θ => g M a ρ r θ) r θ
                     + Γtot M r θ ρ μ b * dCoord ν (fun r θ => g M a ρ r θ) r θ))
      + sumIdx (fun ρ => -Γtot M r θ ρ μ b * dCoord ν (fun r θ => g M a ρ r θ) r θ
                     + Γtot M r θ ρ ν b * dCoord μ (fun r θ => g M a ρ r θ) r θ))) = 0 := by
  -- Use only algebraic reassociation; do NOT unfold any definitions.
  simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
    using h_cancel
exact h_cancel'
```

**Why it works**: Uses only add_* reshuffling (no unfolding), so doesn't change downstream shapes.

### Fix B: Line 9851 - Type Mismatch After Metric Contraction

**Problem**: Metric constant `g M a a r θ` is outside sumIdx, but RHS expects "contract-then-sum" form.

**Paul's Fix**:
```lean
-- Factor the left metric constant through sums in a *single* step
rw [sumIdx_factor_const_from_sub_left,  -- c·(ΣA - ΣB) = c·ΣA - c·ΣB
    mul_sumIdx,                         -- c·Σf = Σ(c·f)
    sumIdx_factor_const_from_sub_right, -- Σ(A·c - B·c) = (ΣA - ΣB)·c
    mul_sumIdx_right]                   -- Σf·c = Σ(f·c)

-- Immediately collapse with the diagonal metric on the correct side
have := sumIdx_collapse_left_metric M r θ (fun ρ => ...) a
-- or, when the metric sits on the right:
-- have := insert_delta_right_diag M r θ b (fun ρ => ...)

-- Use the `_collapse_` helper in the direction that makes your goal
-- (if needed, a single `simp [add_comm, add_left_comm, add_assoc]` to align)
```

**Why it works**: Avoids unfolding g and gets to the shape consumed by downstream Riemann identity lemmas.

### Fix C: Line 9865 - Rewrite Pattern Not Found

**Problem**: Goal has `dCoord μ (X - Y - Z)` shape but not syntactically matching `dCoord_sub_sub_regroup`.

**Paul's Fix**:
```lean
-- Force the syntactic head to match the _regroup lemma
change
  dCoord μ (fun r θ => X r θ - Y r θ - Z r θ) r θ
    = (dCoord μ (fun r θ => X r θ) r θ - dCoord μ (fun r θ => Y r θ) r θ)
      - dCoord μ (fun r θ => Z r θ) r θ
-- Now it matches *syntactically*
simpa using
  dCoord_sub_sub_regroup μ X Y Z r θ
    hXr hYr hZr hXθ hYθ hZθ
```

**Why it works**: Forces syntactic match without new lemmas or global [simp].

### Fix D: Lines 9936 and 10045 - Assumption Failures

**Problem**: Have H with the correct statement, but Lean sees giant match μ/ν expansions and refuses equality.

**Paul's Fix**:
```lean
-- Make a normalized copy; do not touch the goal with `simp` first
have H' := H
-- Normalize *inside H'* only; keep the goal pristine
simp [sub_eq_add_neg,
      nabla_g, Gamma_mu_nabla_nu, Gamma_nu_nabla_mu,
      Riemann, RiemannUp,
      sumIdx_add_distrib, sumIdx_map_sub,
      mul_add, add_mul] at H'
-- Now close the goal by conversion to H'
simpa [sub_eq_add_neg,
       nabla_g, Gamma_mu_nabla_nu, Gamma_nu_nabla_mu,
       Riemann, RiemannUp,
       sumIdx_add_distrib, sumIdx_map_sub,
       mul_add, add_mul] using H'
```

**Tip**: If goal insists on expanding dCoord as nested deriv/match, add @[simp] locally for dCoord_t/r/θ/φ within a short section … end around this closeout block.

**Why it works**: Normalize the statement to the shape of the goal, then simpa.

---

## Implementation Progress

### Completed ✅
1. Revert to 8-error baseline with simple simp-bundle (DONE)
2. Add heartbeat fence at h_pack line 8819 (DONE)
3. Add heartbeat fence at h_delta line 8870 (DONE)

### In Progress ⏸
4. Add heartbeat fence at hb proof (~line 9102) - NEED TO FIND EXACT LOCATION
5. Apply Fix A for line 9650 (h_cancel mismatch)
6. Apply Fix B for line 9851 (metric contraction)
7. Apply Fix C for line 9865 (rewrite pattern)
8. Apply Fix D for lines 9936, 10045 (assumption failures)

### Testing Plan
After each fix group:
1. Rebuild to verify error count decreases
2. Check that no new errors introduced
3. Verify shapes preserved (no cascading failures)

---

## Paul's Key Insights

### Why Deterministic Approaches Failed

1. **Let-bindings change unification shape**:
   - `let F` and `let G` change how Lean unfolds terms
   - Downstream proofs depend on EXACT shape from simple simp
   - Changing h_pack's structure cascades to h_congr, h_delta, and beyond

2. **Simpa with arguments triggers recursion**:
   - `simpa [h₁]` and `simpa using ...` trigger max recursion depth
   - Simple simp with NO arguments is more robust

3. **Change tactic modifies goal state**:
   - Creates shape mismatches in h_congr and beyond
   - Changes definitional equality that downstream proofs expect

4. **Calc block overhead**:
   - Introduces intermediate goals
   - Each step changes unification shape
   - Simple simp does this in ONE STEP with no intermediate state

### Bottom Line

**DO NOT "improve" h_pack**. Fence the heartbeats where needed, and fix the five genuine issues with the shape-preserving rewrites. This keeps the architecture stable and gets past the current block without re-introducing the 22-error state.

---

## Next Steps

1. **Find exact location of hb timeout** (line ~9102)
2. **Add final heartbeat fence** for hb proof
3. **Rebuild to verify** all 3 timeouts resolved
4. **Apply Fixes A-D** one by one
5. **Rebuild after each fix** to verify progress
6. **Report final error count** to Paul

---

## Files

### Main File
`/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean`

**Modified**: Lines 8819, 8870 (heartbeat fences applied)

### Build Logs
- **Baseline**: `build_revert_deterministic_hpack_nov9.txt` (8 errors)
- **After Step 2**: PENDING rebuild

### Reports
- **Critical failure**: `CRITICAL_PAUL_DETERMINISTIC_HPACK_FAILURE_NOV9.md`
- **This plan**: `PAUL_SURGICAL_FIXES_PLAN_NOV9.md`

---

**Report Date**: November 9, 2025
**Agent**: Claude Code (Sonnet 4.5)
**Status**: ⏸ IN PROGRESS - Heartbeat fences applied, surgical fixes pending
