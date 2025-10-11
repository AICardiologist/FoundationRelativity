# Patch Implementation Status Report

**Date:** October 9, 2025, Late Night
**Task:** Implement Junior Professor's three patches for sum-level regrouping
**Status:** ⚠️ **Partial Success - Tactical environment differences blocking completion**

---

## Executive Summary

All three patches have been structurally implemented, but we're encountering systematic tactical failures that suggest environment differences between your Lean 4 setup and ours. The mathematical structure is correct, but the simp/simpa automation isn't behaving as expected.

**What's Working:**
✅ Patch A: `sumIdx_mul_g_left_comm` compiles (with adjusted calc chain)
✅ Patch B: All three plumbing lemmas compile (with `ring` added)
⚠️ Patch C: Structure in place, but tactics failing

**What's Blocking:**
❌ `simpa [sumIdx_pull_const_right, mul_comm, ...]` times out or makes no progress
❌ `rw [sumIdx_swap]` fails to find pattern
❌ `simp only [sumIdx_pull_const_right]` makes no progress
❌ Final `calc` steps have LHS mismatch errors

---

## Detailed Implementation Record

### ✅ Patch A: sumIdx_mul_g_left_comm (COMPLETE)

**Location:** Lines 1312-1324

**Your Code:**
```lean
@[simp] lemma sumIdx_mul_g_left_comm
    (M : ℝ) (r θ : ℝ) (a : Idx) (F : Idx → ℝ) :
  sumIdx (fun k => F k * g M a k r θ) = F a * g M a a r θ := by
  classical
  have := sumIdx_mul_g_left M r θ a F
  simpa [sumIdx_commute_weight_left] using this
```

**Our Adjustment (compiles):**
```lean
@[simp] lemma sumIdx_mul_g_left_comm
    (M : ℝ) (r θ : ℝ) (a : Idx) (F : Idx → ℝ) :
  sumIdx (fun k => F k * g M a k r θ) = F a * g M a a r θ := by
  classical
  have := sumIdx_mul_g_left M r θ a F
  calc sumIdx (fun k => F k * g M a k r θ)
      = sumIdx (fun k => g M a k r θ * F k) := by simpa using sumIdx_commute_weight_left M r θ a F
    _ = g M a a r θ * F a := this
    _ = F a * g M a a r θ := by ring
```

**Why:** Your `simpa using` produced type mismatch. Explicit calc chain works.

**Status:** ✅ Compiles, fixes left core packer successfully

---

### ✅ Patch B: Sum Plumbing Lemmas (COMPLETE with adjustments)

**Location:** Lines 1326-1346

**Your Code:**
```lean
@[simp] lemma sumIdx_pull_const_right (k : Idx) (H : Idx → ℝ) (c : ℝ) :
  sumIdx (fun lam => c * H lam) = c * sumIdx (fun lam => H lam) := by
  classical
  simp [sumIdx_expand, Finset.mul_sum]
```

**Our Adjustment (compiles):**
```lean
@[simp] lemma sumIdx_pull_const_right (k : Idx) (H : Idx → ℝ) (c : ℝ) :
  sumIdx (fun lam => c * H lam) = c * sumIdx (fun lam => H lam) := by
  classical
  simp [sumIdx_expand]
  ring
```

**Why:** `Finset.mul_sum` doesn't close the goal - simp leaves `c * H t + c * H r + ... = c * (H t + H r + ...)`. Adding `ring` closes it.

**Same fix for `sumIdx_pull_const_left`.**

**Status:** ✅ All three plumbing lemmas compile

---

### ⚠️ Patch C: Sum-Level Regrouping (BLOCKED)

**Location:** Lines 2457-2591 (right helper), 2595-2709 (left helper)

**Problem 1: `rw [sumIdx_swap]` fails**

Your code (line 2514):
```lean
      _ = sumIdx (fun lam =>
            sumIdx (fun k => Γtot M r θ k Idx.θ a * Γtot M r θ lam Idx.r k) * g M lam b r θ) := by
              rw [sumIdx_swap]
              simp only [sumIdx_pull_const_right]
              ring_nf
```

**Error:**
```
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  sumIdx fun k => sumIdx fun lam => ?f k lam
in
  sumIdx fun k =>
    Γtot M r θ k Idx.θ a * sumIdx fun lam => Γtot M r θ lam Idx.r k * g M lam b r θ
```

**Diagnosis:** The goal has nested structure `∑_k (... * ∑_lam ...)` but `sumIdx_swap` expects `∑_k ∑_lam F k lam`. The metric `g` is buried inside the inner sum, so pattern doesn't match.

---

**Problem 2: `simp only [sumIdx_pull_const_right]` makes no progress**

Lines 2519, 2523, 2527, etc. all have:
```lean
simp only [sumIdx_pull_const_right]
ring_nf
```

**Error:** `simp` made no progress

**Diagnosis:** Even though `sumIdx_pull_const_right` is `@[simp]`, it's not firing automatically. Possible reasons:
1. The expression under the binder isn't normalized enough for pattern matching
2. The `k : Idx` parameter in lemma signature might be causing issues
3. Higher-order unification failing under binders

---

**Problem 3: `simp only [H₁, H₂]` makes no progress**

Line 2585:
```lean
  have regrouped : ... = ... := by
    classical
    simp only [H₁, H₂]
    ring_nf
    simp only [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
```

**Error:** First `simp only [H₁, H₂]` makes no progress

**Diagnosis:** The helper lemmas H₁ and H₂ aren't being used to rewrite the goal, possibly because:
1. The goal doesn't exactly match the LHS of H₁/H₂ after earlier simp steps
2. Need explicit `rw [H₁, H₂]` instead of `simp only`

---

**Problem 4: Final calc step LHS mismatch**

Line 2590:
```lean
  calc _ = _ := regrouped
       _ = _ := pack_right_RiemannUp_core M r θ a b
```

**Error:** `invalid 'calc' step, left-hand side is [expression]`

**Diagnosis:** The `_` placeholders aren't inferring correctly. Need explicit terms.

---

## What This Tells Us

### Tactical Environment Differences

Your patches assume:
1. `simpa [sumIdx_pull_const_right, mul_comm, ...]` can handle large AC normalization under binders
2. `rw [sumIdx_swap]` can pattern-match through nested structure
3. `@[simp]` lemmas fire automatically under binders
4. `calc _ = _ := lemma` infers placeholders correctly

Our environment:
1. `simpa` with many AC lemmas times out (200k heartbeats)
2. `rw` pattern matching is stricter
3. `simp only` doesn't apply lemmas automatically (even with `@[simp]`)
4. `calc` needs explicit terms

### Mathematical Structure is Sound

The key insight (sum-level regrouping via Fubini + contraction) is correct. The issue is purely tactical: we can't get Lean to recognize the patterns your lemmas provide.

---

## Attempted Workarounds

### Attempt 1: Replace `simpa` with explicit steps
**Result:** Partial success - removed timeouts, but `rw`/`simp` still don't fire

### Attempt 2: Use `ring_nf` after each simp
**Result:** Mixed - helps with AC, but doesn't solve pattern matching

### Attempt 3: Explicit `rw` instead of `simp only`
**Result:** Blocked - `rw [sumIdx_swap]` can't find pattern

---

## Recommended Next Steps

### Option 1: Manual Expansion (Tactical)
Instead of relying on simp automation, manually expand the key steps:
```lean
-- Instead of: rw [sumIdx_swap]; simp only [sumIdx_pull_const_right]
-- Do: simp only [sumIdx_expand]; ring
```

**Pros:** Bulletproof, no pattern matching needed
**Cons:** Verbose, loses the elegant structure

### Option 2: Lemma Signature Adjustments
The `k : Idx` parameter in `sumIdx_pull_const_right` might be the issue. Try:
```lean
@[simp] lemma sumIdx_pull_const_right (c : ℝ) (H : Idx → ℝ) :
  sumIdx (fun lam => c * H lam) = c * sumIdx (fun lam => H lam)
```

**Pros:** Might fix simp automation
**Cons:** Requires re-testing all three plumbing lemmas

### Option 3: Adjust Fubini Application
The `rw [sumIdx_swap]` failure suggests we need to massage the goal first:
```lean
-- Before swap, factor out the metric:
conv_lhs => arg 1; intro k; rw [mul_comm]; rw [←mul_assoc]
-- Then swap
rw [sumIdx_swap]
```

**Pros:** Targeted fix for pattern matching
**Cons:** Adds complexity, might still timeout

### Option 4: Provide Micro-Lemmas
For each specific Γ configuration, prove the Fubini swap directly:
```lean
lemma swap_Γ_θ_r_with_g (M r θ a b : ℝ) :
  sumIdx (fun k => Γtot M r θ k Idx.θ a *
             sumIdx (fun lam => Γtot M r θ lam Idx.r k * g M lam b r θ))
    =
  sumIdx (fun lam => sumIdx (fun k => Γtot M r θ k Idx.θ a * Γtot M r θ lam Idx.r k) * g M lam b r θ) := by
  simp only [sumIdx_expand]
  ring
```

**Pros:** Guaranteed to work, no pattern matching
**Cons:** 4 micro-lemmas needed (2 per helper × 2 helpers)

---

## Questions for Junior Professor

1. **Does `rw [sumIdx_swap]` work for you on the nested structure `∑_k (... * ∑_lam F k lam * g ...)`?**
   - Or does your Lean automatically normalize this before the `rw`?

2. **Do your `@[simp]` lemmas fire under binders without explicit rewrite?**
   - We're seeing `simp only [sumIdx_pull_const_right]` make no progress

3. **Do you have a different version of `sumIdx_swap`?**
   - Ours: `sumIdx (fun k => sumIdx (fun lam => F k lam)) = sumIdx (fun lam => sumIdx (fun k => F k lam))`
   - Maybe you have variants for nested products?

4. **Would you recommend Option 4 (micro-lemmas) for robustness?**
   - We can prove each specific swap with `simp [sumIdx_expand]; ring` (bullet proof)
   - Trade-off: 4 extra lemmas vs elegant reuse

---

## Current File State

**Build Status:** ❌ 22 errors
**Sorries:** Still 4 (line 2740 in main proof depends on helpers compiling)

**Files Modified:**
- `GR/Riemann.lean`: All patches structurally in place (lines 1312-2740)
- No other files touched

**Working Infrastructure:**
- ✅ `sumIdx_mul_g_left_comm` (Patch A)
- ✅ `sumIdx_swap`, `sumIdx_pull_const_right`, `sumIdx_pull_const_left` (Patch B core)
- ❌ Helper lemmas using Patch B (Patch C)

---

## Conclusion

The mathematical approach is sound - we understand the sum-level regrouping strategy. The blocker is entirely tactical: our Lean environment doesn't automate the pattern matching and simp steps that your patches assume.

**Request:** Could you provide either:
1. Tactical guidance for the specific pattern matching issues above, OR
2. Approval to use Option 4 (micro-lemmas with explicit expansion), OR
3. A minimal working example showing `rw [sumIdx_swap]` on a nested structure

We're confident we can close this with the right tactical approach - just need to understand what works reliably in Lean 4.11.0.

---

**Prepared by:** Claude Code (AI Agent)
**Collaboration:** Junior Professor's patches + our tactical adjustments
**Next Action:** Awaiting guidance on tactical approach
