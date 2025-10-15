# Investigation Report - JP's Step 5 Tactical Fixes

**TO:** JP (Junior Professor)
**FROM:** Claude Code (AI Agent)
**DATE:** October 13, 2025
**RE:** Step 5 Implementation Blockers - Expression Mismatch Issue
**BUILD STATUS:** ✅ Clean (0 compilation errors)
**SORRY COUNT:** 11 (unchanged)

---

## EXECUTIVE SUMMARY

**Fix #1 (pair_θ_fold_comm):** ✅ **Successfully implemented** with minor modification
**Fix #2 (Step 5 funext→fold→lift):** ❌ **Blocked** - Expression mismatch between JP's code and our h_weighted

**Root Cause:** JP's drop-in code assumes a specific syntactic form for `h_weighted` that doesn't match what our codebase produces after the compat expansion step.

---

## FIX #1: pair_θ_fold_comm - ✅ WORKING

### Implementation (Lines 6060-6085)

Successfully implemented the negate→fold→re-negate pattern with one modification:

```lean
have pair_θ_unneg :
  Γtot M r θ k Idx.r a * Sθk + Γtot M r θ k Idx.r a * Sθb
    = Γtot M r θ k Idx.r a * dCoord Idx.θ (fun r θ => g M k b r θ) r θ := by
  -- negate both sides of pair_θ and clean up
  have := congrArg (fun x : ℝ => -x) pair_θ
  simp only [neg_add, neg_mul, sub_eq_add_neg, neg_neg] at this  -- ← CHANGED
  exact this  -- ← CHANGED FROM: simpa [...] using this
```

### What We Changed

**Original (from JP):**
```lean
simpa [neg_add, neg_mul, sub_eq_add_neg] using this
```

**Our Fix:**
```lean
simp only [neg_add, neg_mul, sub_eq_add_neg, neg_neg] at this
exact this
```

### Why This Was Needed

`simpa` was expanding the definition of `dCoord (fun r θ => g M k b r θ)` too aggressively, causing a type mismatch. Using `simp only` with a controlled lemma list prevents over-expansion.

**Result:** ✅ Compiles cleanly, zero errors

---

## FIX #2: Step 5 (funext→fold→lift→recognize) - ❌ BLOCKED

### The Problem

JP's Step 5 code (lines 6122-6146 in his message) assumes `h_weighted` has a specific form after Step 4:

**Expected form (from JP's code):**
```lean
sumIdx (fun k =>
  dCoord Idx.r (Γtot k Idx.θ a) * g k b
  - dCoord Idx.θ (Γtot k Idx.r a) * g k b
  + (sumIdx (fun lam => Γ k Idx.r lam * Γ lam Idx.θ a)) * g k b
  - (sumIdx (fun lam => Γ k Idx.θ lam * Γ lam Idx.r a)) * g k b
)
```

**Key assumption:** Inner `sumIdx (fun lam => ...)` expressions still present as sums.

### What Our Code Actually Produces

After Step 3 (compat expansion with `dCoord_g_via_compat_ext`), the expressions have a different syntactic form that doesn't match JP's expected LHS.

**With Step 4 collapse (sumIdx_Γ_g_left/right):**
The collapse lemmas contract the inner sums:
```lean
sumIdx_Γ_g_left: sumIdx (fun e => Γ e x a * g e b) = Γ b x a * g b b
sumIdx_Γ_g_right: sumIdx (fun e => Γ e x b * g a e) = Γ a x b * g a a
```

This eliminates the `sumIdx (fun lam => ...)` that JP's fold expects to factor.

**Without Step 4 collapse:**
Even without collapse, `h_weighted` after Step 3 doesn't match JP's h_bracket_fiber LHS - the compat expansions produce a different syntactic structure.

---

## ATTEMPTS MADE (All Failed)

### Attempt 1: Use collapse + direct fold
```lean
simp_rw [sumIdx_Γ_g_left M r θ, sumIdx_Γ_g_right M r θ] at h_weighted
simp only [fold_sub_right, fold_add_left] at h_weighted
exact h_weighted
```
**Result:** Type mismatch - collapsed form doesn't match goal

### Attempt 2: Use collapse + RiemannUp recognition
```lean
simp_rw [sumIdx_Γ_g_left M r θ, sumIdx_Γ_g_right M r θ] at h_weighted
simp [RiemannUp] at h_weighted
exact h_weighted
```
**Result:**
```
error: Tactic `simp` failed with a nested error:
maximum recursion depth has been reached
```

### Attempt 3: Skip collapse, use JP's funext approach directly
```lean
-- Skip: simp_rw [sumIdx_Γ_g_left M r θ, sumIdx_Γ_g_right M r θ] at h_weighted

have h_bracket_fiber : [JP's exact code from message]
  funext k
  simp [fold_sub_right, fold_add_left, sub_eq_add_neg,
        add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm, mul_assoc]
```
**Result:**
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:6137:26: unsolved goals
```
The funext + simp leaves unsolved goals.

### Attempt 4: Complete JP's pattern with sumIdx_congr_then_fold
```lean
have h_bracket_sum := sumIdx_congr_then_fold h_bracket_fiber
have h_finish := h_weighted.trans h_bracket_sum
simp only [RiemannUp] at h_finish
exact h_finish
```
**Result:**
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:6144:36: Application type mismatch:
The argument h_bracket_sum has type [...]
but is expected to have type [...]
```

### Attempt 5: Direct RiemannUp unfolding
```lean
simp only [RiemannUp] at h_weighted
exact h_weighted
```
**Result:** `simp made no progress`

---

## ROOT CAUSE ANALYSIS

### The Core Issue

JP's drop-in code was written **generically** without seeing our actual codebase. The code assumes:

1. After compat expansion (Step 3), `h_weighted` has inner sums in the form `sumIdx (fun lam => Γ * Γ)`
2. These inner sums remain as `sumIdx` expressions (not contracted)
3. The syntactic structure matches the LHS of `h_bracket_fiber` exactly

**Reality:** Our `dCoord_g_via_compat_ext` lemma produces expressions in a specific form that differs from JP's assumptions. The syntactic mismatch prevents pattern matching.

### Why This Matters

Lean 4 requires **exact syntactic matching** for rewrites and pattern matching. Even if two expressions are mathematically equal, if they're not in the same syntactic form (modulo AC-normalization), tactics like `rw`, `simp`, and `exact` will fail.

---

## COMPARISON: OLD vs NEW Approach

### OLD Working Approach (Lines 2678-2850)

The OLD regroup lemma uses a different strategy:
1. Pointwise compat rewrites with `have compat_r_e_b : ∀ e, [equality]`
2. `simp_rw [compat_r_e_b, compat_θ_e_b]` to expand ∂g
3. Manual Fubini swaps with helper lemmas H₁, H₂
4. Pointwise kk_refold with `funext k; rw [Hr, Hθ]`
5. Direct contraction and `ring`

**Status:** ✅ Works, but has OLD structure (not weighted-first)

### NEW Weighted-First Approach (Lines 5867-6133)

JP's approach tries to:
1. Stop fiber at Γ*∂g form (not RiemannUp bracket)
2. Lift to sum level immediately
3. Expand compat under outer sum
4. Collapse inner λ-sums
5. Fold to bracket form fiberwise, then lift

**Status:** ⏳ Steps 1-3 work, Steps 4-5 blocked on expression mismatch

---

## WHAT WE KNOW ABOUT h_weighted

After Step 3 (`simp_rw [dCoord_g_via_compat_ext M r θ h_ext] at h_weighted`):

**Goal LHS (what we're trying to prove):**
```lean
sumIdx (fun k =>
  dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a * g M k b r θ) r θ
  - dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a * g M k b r θ) r θ)
```

**Goal RHS:**
```lean
sumIdx (fun k => RiemannUp M r θ k a Idx.r Idx.θ * g M k b r θ)
```

**h_weighted LHS (after fiber proof + lift):**
```lean
sumIdx (fun k =>
  dCoord Idx.r (Γtot k Idx.θ a) * g k b
  - dCoord Idx.θ (Γtot k Idx.r a) * g k b
  + (Γ k Idx.θ a * ∂ᵣg_{kb} - Γ k Idx.r a * ∂_θg_{kb})
)
```

**h_weighted RHS (should equal goal RHS after compat + fold):**
```lean
sumIdx (fun k =>
  [Some expression with expanded ∂g terms using compat]
)
```

**What we need:** The exact form of h_weighted.RHS after Step 3 to know what LHS to match in h_bracket_fiber.

---

## NEXT STEPS - THREE OPTIONS

### Option A: Debug Expression Dump (Recommended)

**Add tactic to see exact goal state:**
```lean
-- After Step 3
simp_rw [dCoord_g_via_compat_ext M r θ h_ext] at h_weighted

-- DEBUG: Inspect h_weighted
trace "{h_weighted}"  -- or use #check or show_term
sorry
```

**Output the actual expression**, then:
1. Write h_bracket_fiber.LHS to match the ACTUAL h_weighted form
2. Adjust fold lemmas to match actual syntactic structure
3. Complete the proof with corrected expressions

**Effort:** Medium (1-2 hours debugging)
**Success probability:** High (we control the expressions)

### Option B: Revert to OLD Working Approach

**Use the proven tactics from lines 2678-2850:**
1. Keep Steps 1-2 (fiber stop at Γ*∂g, lift to sum level)
2. Replace Steps 3-5 with OLD approach:
   - Pointwise compat rewrites
   - Manual Fubini with H₁/H₂ lemmas
   - Pointwise kk_refold with targeted `rw`
   - Contract and `ring`

**Effort:** Low (copy-paste + adapt)
**Success probability:** High (OLD code compiles)
**Downside:** Not as clean as weighted-first

### Option C: Ask JP for Help with Expression Dump

**Provide JP with:**
1. Exact h_weighted expression after Step 3 (from trace)
2. The compat lemma we use: `dCoord_g_via_compat_ext`
3. The collapse lemmas: `sumIdx_Γ_g_left`, `sumIdx_Γ_g_right`
4. Request: "Please write h_bracket_fiber.LHS to match this specific form"

**Effort:** Low (document + wait)
**Success probability:** High (JP knows the math)
**Downside:** Blocks on JP's availability

---

## RECOMMENDATION

**Pursue Option A first** (debug expression dump), with Option B as fallback.

**Reasoning:**
1. We've already made significant progress (Steps 1-3 working)
2. The weighted-first approach is structurally sound
3. The issue is purely syntactic/tactical, not mathematical
4. We can see the expressions ourselves and fix them
5. If stuck after 1-2 hours, revert to Option B (known working approach)

**Avoid Option C** unless Options A and B both fail - we should exhaust self-debugging first.

---

## CODE LOCATIONS

**Current implementation:** `GR/Riemann.lean` lines 5867-6133

**Key sections:**
- Lines 6053-6058: pair_r_fold_comm ✅ Working
- Lines 6060-6085: pair_θ_fold_comm ✅ Working
- Lines 6092-6098: Weighted-first lift + compat expansion ✅ Working
- Lines 6100-6103: Step 1 (distribute) ✅ Working
- Lines 6115-6133: Steps 4-5 ❌ **BLOCKED HERE**

**OLD working approach:** Lines 2678-2850 (for reference)

---

## BUILD STATUS

✅ **Clean Build:** 0 compilation errors
✅ **Sorry Count:** 11 (same as before, no regression)
✅ **Commit:** 8ef4767 - Investigation results documented

---

## TECHNICAL DETAILS

### The sumIdx_Γ_g Collapse Lemmas

```lean
@[simp] lemma sumIdx_Γ_g_left (M r θ : ℝ) (x a b : Idx) :
  sumIdx (fun e => Γtot M r θ e x a * g M e b r θ)
    = Γtot M r θ b x a * g M b b r θ

@[simp] lemma sumIdx_Γ_g_right (M r θ : ℝ) (x a b : Idx) :
  sumIdx (fun e => Γtot M r θ e x b * g M a e r θ)
    = Γtot M r θ a x b * g M a a r θ
```

These contract sums by setting the bound variable equal to a free variable (metric contraction).

**Problem:** After collapse, we have `Γ b x a * g b b` instead of `sumIdx (fun lam => Γ k x lam * Γ lam y a)`.

JP's fold expects to factor:
```
A * g + B * g = (A + B) * g
```

But after collapse we have:
```
C * g_bb + D * g_bb = [not the form we want]
```

### The RiemannUp Definition

```lean
def RiemannUp (M r θ : ℝ) (a b c d : Idx) : ℝ :=
  dCoord c (fun r θ => Γtot M r θ a d b) r θ
  - dCoord d (fun r θ => Γtot M r θ a c b) r θ
  + sumIdx (fun e => Γtot M r θ a c e * Γtot M r θ e d b)
  - sumIdx (fun e => Γtot M r θ a d e * Γtot M r θ e c b)
```

Our goal RHS is:
```lean
sumIdx (fun k => RiemannUp M r θ k a Idx.r Idx.θ * g M k b r θ)
```

Expanding RiemannUp with (a=k, b=a, c=Idx.r, d=Idx.θ):
```lean
sumIdx (fun k =>
  (dCoord Idx.r (Γ k Idx.θ a) - dCoord Idx.θ (Γ k Idx.r a)
   + sumIdx (fun e => Γ k Idx.r e * Γ e Idx.θ a)
   - sumIdx (fun e => Γ k Idx.θ e * Γ e Idx.r a))
  * g k b
)
```

This is the target form we need to reach.

---

## CONCLUSION

**Summary:**
- ✅ pair_θ_fold_comm works with minor fix (simp only + exact)
- ❌ Step 5 blocked on expression mismatch
- 🔍 Need to inspect h_weighted's actual form to write matching fold

**Next Action:**
Implement Option A (debug expression dump) to see what h_weighted actually looks like, then write custom fold that matches our specific syntactic form.

**Status:** Ready to proceed with debugging once we get green light.

---

**Respectfully submitted,**
Claude Code (AI Agent)
October 13, 2025

**Attachments:**
- Code: `GR/Riemann.lean` lines 5867-6133
- Commit: 8ef4767
- Build: ✅ Clean
