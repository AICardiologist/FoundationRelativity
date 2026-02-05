# Diagnostic Report: JP's Third Patch Implementation

**Date:** October 9, 2025
**Status:** ❌ **Build Failing - Tactical Mismatch**

---

## Issue Summary

JP's latest tactical recipe doesn't match our actual goal structure after `simp_rw [compat_*]` and distribution.

**Expected (per JP's recipe):**
After distribution, goal has 4 Γ·(∑Γ·g) terms (only "right-slot" branches)

**Actual (in our proof):**
After distribution, goal has **8 Γ·(∑Γ·g) terms** (BOTH "right-slot" AND "left-slot" branches from the two-branch compat expansion)

---

## Root Cause

The compat expansion produces TWO branches per ∂g term:
```
∂_c g_{eb} = ∑_k Γ_{kce} * g_{kb}  +  ∑_k Γ_{kcb} * g_{ek}
             └─────right-slot─────┘    └─────left-slot─────┘
```

After `simp_rw [compat_r_e_b, compat_θ_e_b]`:
- `Γ_{kθa} * ∂_r g_{kb}` expands to 2 terms
- `Γ_{kra} * ∂_θ g_{kb}` expands to 2 terms

Total: 2 dCoord·Γ·g terms (unchanged) + 2×2 = **4 Γ·∑Γ·g terms** per compat × 2 compats = **8 Γ·∑Γ·g terms**

---

## JP's Assumption vs Reality

**JP's recipe assumes:**
```lean
-- After distribution:
sumIdx (fun k =>
    ∂_r Γ_{kθa} * g_{kb}
  - ∂_θ Γ_{kra} * g_{kb}
  + Γ_{kθa} * (∑_lam Γ_{lam r k} * g_{lam b})   -- RIGHT-slot only
  - Γ_{kra} * (∑_lam Γ_{lam θ k} * g_{lam b}))  -- RIGHT-slot only
```

**Our actual goal after distribution:**
```lean
sumIdx (fun k =>
    ∂_r Γ_{kθa} * g_{kb}
  - ∂_θ Γ_{kra} * g_{kb}
  + Γ_{kθa} * (∑_lam Γ_{lam r k} * g_{lam b})   -- RIGHT-slot from +branch
  + Γ_{kθa} * (∑_lam Γ_{lam r b} * g_{k lam})   -- LEFT-slot from +branch
  - Γ_{kra} * (∑_lam Γ_{lam θ k} * g_{lam b})   -- RIGHT-slot from -branch
  - Γ_{kra} * (∑_lam Γ_{lam θ b} * g_{k lam}))  -- LEFT-slot from -branch
```

---

## Why JP's `split` Lemma Fails

**The `split` lemma tries to prove:**
```lean
LHS (4 terms) = RHS_part1 (2 terms) + RHS_part2 (2 terms)
```

**But after distribution we actually have:**
```lean
LHS (6 terms: 2 dCoord + 4 Γ·∑Γ·g)
```

The simp can't match because there are **extra terms** (the left-slot branches) that JP's recipe doesn't account for.

---

## Why the Mismatch Occurred

**Hypothesis:** JP's recipe was written for a DIFFERENT lemma statement that DOESN'T use compat expansion with two branches.

**Evidence:**
1. JP says "never fire sumIdx_Γ_g_left/right" - correct, we shouldn't collapse
2. JP says "keep both compat branches intact" - we are doing this
3. But JP's `split` LHS only has 4 Γ·∑Γ·g terms, not 8

**Conclusion:** JP might have been thinking of a version where:
- We use a DIFFERENT compatibility lemma that only produces one branch, OR
- We manually eliminate the left-slot branches BEFORE the split step

---

## Two Possible Solutions

### Option A: Add kk_cancel BEFORE split
```lean
-- After distribution, eliminate left-slot branches first
have elim_left :
  sumIdx (fun k =>
      ... + Γ * (∑ Γ * g_{k lam})  -- left-slot +
      ... - Γ * (∑ Γ * g_{k lam})) -- left-slot -
  = sumIdx (fun k =>
      ... -- no left-slot terms
  ) := by
  -- Use kk_cancel to show left-slot terms = 0
  ...

-- THEN apply JP's split/gather/regrouped
```

### Option B: Adjust split to handle 8 terms
```lean
have split :
  sumIdx (fun k =>
      dCoord ... * g
    - dCoord ... * g
    + Γ * (∑ Γ * g_{lam b})  -- right +
    + Γ * (∑ Γ * g_{k lam})  -- left +
    - Γ * (∑ Γ * g_{lam b})  -- right -
    - Γ * (∑ Γ * g_{k lam})) -- left -
  =
    (dCoord + dCoord)  -- part 1
  + (right + - right -)  -- part 2
  + (left + - left -)  -- part 3 (will cancel)
```

Then show part 3 = 0, and proceed with gather on part 2 only.

---

## Recommended Action

**I recommend Option A** because:
1. It matches JP's earlier guidance about needing kk_cancel
2. It's cleaner - eliminate noise first, then proceed
3. JP's gather/regrouped steps will work unchanged

**Implementation:**
1. After distribution step (line 2492), add kk_cancel elimination
2. Then proceed with JP's split/gather/regrouped exactly as written

---

## Error Details

**Build errors:**
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:2552:76: unsolved goals
```

**Line 2552:** End of `split` have statement

**Cause:** The simp can't close the goal because LHS has 6 terms but RHS has only 4 terms in the structure JP specified.

---

## Next Steps

1. Clarify with JP: Does the recipe assume we've already eliminated left-slot branches?
2. If yes: Implement kk_cancel first, then apply split/gather/regrouped
3. If no: Adjust split to explicitly handle all 8 Γ·∑Γ·g terms

---

**Prepared by:** Claude Code (AI Agent)
**Date:** October 9, 2025
**Status:** Awaiting clarification or implementing Option A

