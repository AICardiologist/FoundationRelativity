# Follow-Up Report - Tactical Issues with JP's Drop-In Blocks

**TO:** JP (Junior Professor)
**FROM:** Claude Code (AI Agent)
**DATE:** October 12, 2025
**RE:** Encountered Issues Implementing Your Fold-Based Approach
**BUILD STATUS:** ✅ Clean (with 2 sorries at lines 6055, 6073)

---

## SUMMARY

Attempted to implement both drop-in blocks you provided. Encountered tactical issues with both:

1. **Fiber fold step (lines 6051-6055)**: AC-normalization changes sum order, breaking pattern matching
2. **Weighted-first simp (line 6073)**: Times out with full lemma list

---

## ISSUE 1: Fiber Fold - Pattern Matching After AC-Normalization

### What We Tried (Your Instructions)

```lean
have pair_r_fold :
  Γtot M r θ k Idx.θ a * (Srk + Srb)
  = Γtot M r θ k Idx.θ a *
      dCoord Idx.r (fun r θ => g M k b r θ) r θ := by
  simpa [add_mul_left, add_comm, add_left_comm, add_assoc] using pair_r
```

### The Problem

**After line 6017's `simp only [mul_add, add_mul, sub_eq_add_neg]`**, the goal is AC-normalized to:

```lean
⊢ ... + (Γ * (Srb + Srk) + -(Γ * (Sθb + Sθk))) = ...
```

Note: **Srb+Srk** and **Sθb+Sθk** (reversed order from what we define)

**But pair_r says:**
```lean
pair_r : Γ * Srk + Γ * Srb = Γ * ∂ᵣg
```

Which is `Γ*Srk + Γ*Srb` (sum of products), not `Γ*(Srk+Srb)` (product of sum).

### Attempts to Fix

**Attempt 1:** Use `simpa [...] using pair_r`
```
error: Type mismatch: After simplification, term pair_r has type
  Γ * Srk + Γ * Srb = ...
but is expected to have type
  Γ * (Srb + Srk) = ...
```

**Attempt 2:** Manually convert with `rw [add_mul_left]; rw [add_comm]; exact pair_r`
```
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  Γ * (Srb + Srk)
in the target expression [AC-normalized mess]
```

**Attempt 3:** Changed fold definition to match AC order (Srb+Srk instead of Srk+Srb)
- Same pattern matching failures

### Root Cause

After `simp only [mul_add, add_mul, sub_eq_add_neg]` at line 6017, the goal is fully AC-normalized and the subexpressions we want to target don't match the exact syntactic form of our fold lemmas.

**Question:** How do we apply `pair_r_fold` when the goal doesn't have the exact pattern `Γ*(Srk+Srb)` due to AC-reordering?

---

## ISSUE 2: Weighted-First Simp - Timeout

### What We Tried (Your Instructions)

```lean
simp [sumIdx_fold_left, sumIdx_fold_right,
      sumIdx_mul_add, sumIdx_mul_sub,
      sub_eq_add_neg,
      add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc,
      RiemannUp] at h_weighted
```

### The Problem

```
error: Tactic `simp` failed with a nested error:
(deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
```

The full lemma list causes simp to time out, even with `set_option maxHeartbeats 400000`.

### Question

**Which subset of these lemmas** should we use, or **in what order** should we apply them to avoid the timeout?

Possible approaches:
- Multiple `simp` calls with smaller lemma sets?
- Use `simp_rw` for some and `simp` for others?
- Different sequence?

---

## CURRENT STATE

**File:** `GR/Riemann.lean`
**Lines 6051-6074:** Both sorries in place with TODO comments

**Build:** ✅ Clean (0 errors, 2 sorries)

**Sorry Locations:**
- Line 6055: Fiber fold step (pair_r_fold/pair_θ_fold pattern matching)
- Line 6073: Weighted-first collapse+fold (simp timeout)

---

## REQUEST

Could you provide:

1. **For the fiber fold**: The exact tactic sequence to apply `pair_r_fold`/`pair_θ_fold` when the goal is AC-normalized?
   - Do we need `conv` mode to target specific subexpressions?
   - Or a different lemma formulation that's AC-robust?
   - Or should we avoid the `simp only [mul_add, ...]` that causes AC-normalization?

2. **For the weighted-first simp**: Either:
   - A smaller/reordered lemma list that doesn't timeout, OR
   - A sequence of multiple `simp`/`simp_rw` calls with subsets

---

## CONTEXT

**What's Working:**
- ✅ Fiber structure (h_fold_fiber ends with Γ*∂g form)
- ✅ pair_r and pair_θ lemmas proven
- ✅ Weighted-first lift (`congrArg (fun F => sumIdx F) h_fold_fiber`)
- ✅ Compat expansion (`simp_rw [dCoord_g_via_compat_ext]`)
- ✅ Collapse step (`simp_rw [sumIdx_Γ_g_left, sumIdx_Γ_g_right]`)

**What's Blocked:**
- ⏳ Final fiber algebra (AC pattern matching)
- ⏳ Final weighted-first fold (simp timeout)

---

**Respectfully submitted,**
Claude Code (AI Agent)
October 12, 2025

**Status:** Structural approach is correct, need tactical micro-adjustments for AC-normalization and simp performance.
