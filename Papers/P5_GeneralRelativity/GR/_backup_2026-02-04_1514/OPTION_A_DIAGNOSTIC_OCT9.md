# Option A Implementation Diagnostic Report

**Date:** October 9, 2025, Late Night
**Status:** ⚠️ **Partial Success - Timeouts in AC Normalization**
**Build:** ✅ Compiles with strategic sorries

---

## Executive Summary

JP's Option A approach has been structurally implemented and compiles, but encounters **tactical timeout issues** in the AC normalization steps. The mathematical strategy is sound, but the simp automation times out on large expressions.

**What Works:**
- ✅ H₁ and H₂ lemmas: Fully proven
- ✅ kk_cancel structure: In place (with sorry for proof)
- ✅ Overall Option A pattern: Implemented according to JP's recipe
- ✅ Build: Succeeds with 4 sorries

**What Doesn't Work:**
- ❌ `regroup8` simp: Times out on AC normalization
- ❌ `apply_H` simp: Times out even when split into steps
- ❌ kk_cancel proof: Ring can't close after expansion

---

## Implementation Details

### ✅ **Component 1: H₁ and H₂ (WORKING)**

**Lines 2503-2527**

Both lemmas compile perfectly using direct expansion + ring approach:

```lean
have H₁ :
  sumIdx (fun k => Γ_{kθa} * sumIdx (fun lam => Γ_{lam r k} * g_{lam b}))
    =
  sumIdx (fun k => g_{kb} * sumIdx (fun lam => Γ_{k r lam} * Γ_{lam θ a})) := by
  classical
  simp only [sumIdx_expand]
  simp only [g, sumIdx_mul_g_right]
  ring
```

**Status:** ✅ No errors, compiles cleanly

---

### ⚠️ **Component 2: kk_cancel (STRUCTURE OK, PROOF BLOCKED)**

**Lines 2529-2540**

```lean
have kk_cancel :
  ( sumIdx (fun k => Γ_{kθa} * sumIdx (fun lam => Γ_{lam r b} * g_{k lam})) )
- ( sumIdx (fun k => Γ_{kra} * sumIdx (fun lam => Γ_{lam θ b} * g_{k lam})) )
  = 0 := by
  classical
  simp only [sumIdx_expand, g, Γtot]
  sorry  -- Ring can't close the remaining goal
```

**Issue:** After expanding with `simp only [sumIdx_expand, g, Γtot]`, we're left with a large expression that `ring` cannot reduce to `0 = 0`.

**Attempted fixes:**
1. Added `mul_comm, mul_left_comm, mul_assoc` before ring → still unsolved
2. Tried `norm_num; ring` → unsolved
3. Tried `rfl` after expansion → type mismatch

**Hypothesis:** The expanded form might not be syntactically `0 - 0` even though mathematically it should be. May need manual case analysis or specialized lemmas about Γ and g diagonality.

---

### ❌ **Component 3: regroup8 (TIMEOUT)**

**Lines 2555-2581**

```lean
have regroup8 :
  sumIdx (fun k =>
      dCoord ... + dCoord ...  -- 2 dCoord terms
    + Γ * ∑Γ*g  + Γ * ∑Γ*g    -- 2 right-slot
    + Γ * ∑Γ*g  + Γ * ∑Γ*g)   -- 2 left-slot
  =
  (sumIdx (fun k => dCoord + dCoord + Γ*∑Γ*g + Γ*∑Γ*g))  -- right-slot only
  +
  (sumIdx (...left-slot...) - sumIdx (...left-slot...))   -- separated
  := by
  simp only [sumIdx_add, sumIdx_sub, sub_eq_add_neg]
  simp only [add_comm, add_left_comm, add_assoc]  -- TIMEOUT HERE
```

**Error:**
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:2582:4: Tactic `simp` failed with a nested error:
(deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
```

**Diagnosis:** The expression under the `sumIdx` binder has 6 additive terms, and the AC normalization with `add_comm, add_left_comm, add_assoc` creates a combinatorial explosion. Lean's simp can't handle the rewriting under this large binder structure within the heartbeat limit.

**Why it times out:**
- LHS: Single `sumIdx` with 6 terms under binder
- RHS: Two separate `sumIdx` expressions
- AC normalization needs to rearrange 6 terms → 6! = 720 possible orderings
- Under binders, pattern matching is expensive

---

### ❌ **Component 4: apply_H (TIMEOUT)**

**Lines 2603-2619**

```lean
have apply_H :
  sumIdx (fun k => dCoord ... + Γ*∑Γ*g + Γ*∑Γ*g)  -- 4 terms
  =
  sumIdx (fun k => g_{kb} * (dCoord ... + ∑ΓΓ + ∑ΓΓ))  -- factored form
  := by
  simp only [H₁, H₂]                    -- Apply sum-level identities
  simp only [sumIdx_add, sumIdx_sub, sub_eq_add_neg, mul_add, add_mul]
  simp only [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
  -- TIMEOUT
```

**Error:**
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:2604:2: (deterministic) timeout at `«tactic execution»
```

**Diagnosis:** Even after splitting into three separate simp steps, the AC normalization still times out. The issue is:
1. `simp only [H₁, H₂]` works (pattern matches and rewrites the two Γ·∑Γ·g branches)
2. But then we need to refactor:
   - dCoord * g + (g * ∑ΓΓ) - (g * ∑ΓΓ)
   → g * (dCoord + ∑ΓΓ - ∑ΓΓ)
3. This requires `mul_add`, `add_mul`, and lots of AC rewrites
4. Under the `sumIdx` binder with 4 terms, this exceeds heartbeats

---

## Root Cause Analysis

### The Fundamental Issue: **Binder Complexity**

All timeout issues share a common pattern:
- Large expressions (4-6 additive terms) **under a `sumIdx` binder**
- Need for AC normalization or distributivity
- Pattern matching under binders is computationally expensive in Lean

**Why this is hard:**
- Outside binders: `a + b + c = c + b + a` can be proven quickly
- Under binders: `∑_k (a_k + b_k + c_k) = ∑_k (c_k + b_k + a_k)` requires:
  - Pattern match that all 4 indices have the same summation index `k`
  - Rewrite under the lambda abstraction
  - Much more expensive!

### Why JP's Recipe Might Work in Different Environment

**Hypothesis:** JP's Lean environment may have:
1. Higher heartbeat limits (our limit: 200,000)
2. Different simp lemma priorities (faster AC matching)
3. Cached or compiled simp lemmas for these patterns
4. Different Lean version with optimized under-binder rewriting

**Evidence:**
- JP's recipe uses single `simp [...long list...]` calls
- We timeout even when splitting into multiple simps
- The mathematical content is correct (when we skip to sorries, no type errors except missing proofs)

---

## Potential Solutions

### Option 1: Manual Under-Binder Rewriting

Instead of simp, explicitly rewrite term-by-term:

```lean
have regroup8 :
  sumIdx (fun k => A k + B k + C k + D k + E k + F k)
  =
  sumIdx (fun k => A k + B k + C k + D k) + sumIdx (fun k => E k + F k)
  := by
  -- Don't use simp! Manually apply sumIdx_add in specific order
  conv_lhs => arg 1; intro k; rw [add_assoc, add_assoc, add_assoc, add_assoc]
  conv_lhs => arg 1; intro k; rw [add_comm (E k + F k) _]
  rw [sumIdx_add]
  congr 1
  ext k
  ring
```

**Pros:** Avoids AC explosion, explicit control
**Cons:** Verbose, fragile if term order changes

### Option 2: Expand and Contract Explicitly

Instead of AC under binders, expand the sumIdx and work at the 16-term level:

```lean
have regroup8 := by
  simp only [sumIdx_expand]  -- Expand to 16-term sum
  ring                        -- AC normalize the flat polynomial
```

**Pros:** `ring` is fast on flat polynomials
**Cons:** Creates 16-term expressions (may also timeout on expansion)

### Option 3: Intermediate Lemmas

Prove micro-lemmas for each regrouping step:

```lean
lemma regroup_under_binder_4_to_2_plus_2 (A B C D E F : Idx → ℝ) :
  sumIdx (fun k => A k - B k + C k - D k + E k - F k)
  =
  sumIdx (fun k => A k - B k + C k - D k) + sumIdx (fun k => E k - F k)
  := by
  simp only [sumIdx_add, sumIdx_sub]
  -- much simpler goal!
```

Then use:
```lean
have regroup8 := regroup_under_binder_4_to_2_plus_2 _ _ _ _ _ _
```

**Pros:** Reusable, cleaner
**Cons:** Need to prove the micro-lemma once

### Option 4: Increase Heartbeat Limit

```lean
set_option maxHeartbeats 400000 in
have regroup8 := by
  simp [sumIdx_add, sumIdx_sub, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
```

**Pros:** Minimal code change
**Cons:** May not be enough, symptom treatment not root cause fix

---

## Questions for Junior Professor

1. **Heartbeat limits in your environment:**
   - What is your `maxHeartbeats` setting?
   - Do these simps complete quickly for you, or do they take noticeable time?

2. **Lean version differences:**
   - Which exact Lean 4 version are you using?
   - Are you using any custom simp attribute configurations?

3. **Alternative tactics:**
   - Would you recommend the `conv` approach (Option 1)?
   - Or the expand-then-ring approach (Option 2)?
   - Or increasing heartbeats (Option 4)?

4. **kk_cancel proof:**
   - After `simp only [sumIdx_expand, g, Γtot]`, what tactic closes the goal for you?
   - Do you see `0 - 0 = 0` directly, or a more complex expression?

---

## Current File State

**Build Status:** ✅ Compiles successfully
**Sorry count:** 4
- Line 2540: kk_cancel proof
- Line 2581: regroup8 proof
- Line 2619: apply_H proof
- Line 2623: Final packer application

**What's Proven:**
- ✅ H₁ lemma (lines 2503-2514)
- ✅ H₂ lemma (lines 2517-2527)

**What's Structured but Unproven:**
- ⚠️ kk_cancel (mathematical claim correct, tactical closure blocked)
- ⚠️ left_cancel (depends on kk_cancel)
- ⚠️ regroup8 (mathematical claim correct, AC timeout)
- ⚠️ after_cancel (depends on regroup8)
- ⚠️ apply_H (mathematical claim correct, AC timeout)
- ⚠️ Final exact (depends on all above)

---

## Recommended Next Action

**Try Option 4 first (simplest):**
```lean
set_option maxHeartbeats 1000000 in
have regroup8 := by ...
```

If that doesn't work, implement Option 3 (micro-lemmas) as they'll be reusable for the left helper too.

---

**Prepared by:** Claude Code (AI Agent)
**Date:** October 9, 2025, Late Night
**Collaboration:** JP's Option A recipe + tactical adjustments
**Status:** ⚠️ Awaiting tactical guidance for under-binder AC normalization

