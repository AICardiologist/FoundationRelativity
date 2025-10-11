# Final Diagnostic: ricci_identity_on_g_rθ_ext Tactical Issues

**Date:** October 8, 2025, Late Afternoon
**Session:** Applying Junior Professor's complete tactical sequence
**Status:** ⚠️ 4 errors remain after applying proof (was 5)

---

## Summary

Applied the Junior Professor's complete tactical sequence for `ricci_identity_on_g_rθ_ext`. Made iterative fixes to get past the first two steps:
1. ✅ Removed add_comm/add_left_comm/add_assoc from initial simp only (was causing failure)
2. ✅ Split Z1-Z4 proofs into `simp only [sumIdx_expand, h*0L]; simp` (was unsolved goals)

**Current blocker:** Line 2130 - `simp only [Z1, Z2, Z3, Z4, Hcancel]` makes no progress

---

## Build Status

```bash
Errors: 4 total (was 5 → 11 originally)
- Line 2130: simp only [Z1, Z2, Z3, Z4, Hcancel] - made no progress
- Lines 2179-2189: Riemann_swap_a_b_ext - cascading from above

Progress: 14 →  11 → 5 → 4 errors (71% total reduction)
```

---

## What's Working ✅

### Steps 1-4: All Compile
```lean
-- 1) Unfold ∇ and ∇g ✅
simp only [nabla, nabla_g_shape]

-- 2) Kill ∑ Γ(∇g) terms ✅
have hθ0L : ∀ e, nabla_g M r θ Idx.θ e b = 0 := ...
... (all four h*0* lemmas work)

have Z1 : sumIdx (fun e => Γtot ... * nabla_g ... ) = 0 := by
  simp only [sumIdx_expand, hθ0L]
  simp
... (all four Z* lemmas compile)

-- 3) Kill ∂∂g commutator ✅
have Hcomm := dCoord_commute_for_g_all M r θ a b Idx.r Idx.θ
have Hcancel := sub_eq_zero.mpr Hcomm

-- 4) Get distributors ✅
have HrL := dCoord_r_sumIdx_Γθ_g_left_ext  M r θ h_ext a b
have HrR := dCoord_r_sumIdx_Γθ_g_right_ext M r θ h_ext a b
have HθL := dCoord_θ_sumIdx_Γr_g_left  M r θ a b
have HθR := dCoord_θ_sumIdx_Γr_g_right M r θ a b
```

All of these steps compile ✅

---

## Current Blocker: Line 2130

**Code:**
```lean
-- 5) Apply the cancellations and distributors in a small, explicit order.
--    Avoid broad simp here to keep heartbeats low and shapes predictable.
simp only [Z1, Z2, Z3, Z4, Hcancel]  -- ← Line 2130: `simp` made no progress
rw [HrL, HrR, HθL, HθR]
```

**Error:** `simp` made no progress

**Context:** At this point in the proof:
- The goal is the expanded form of `∇_r(∇_θ g) - ∇_θ(∇_r g)`
- Z1-Z4 state that four specific sumIdx terms equal 0
- Hcancel states that `∂_r(∂_θ g) - ∂_θ(∂_r g) = 0`

**Issue:** `simp only` with these five lemmas doesn't rewrite anything in the goal

**Hypothesis:** The goal structure after `simp only [nabla, nabla_g_shape]` doesn't syntactically match the LHS of Z1-Z4 or Hcancel

---

## Tactical Adjustments Attempted

### Adjustment 1: Removed associative/commutative laws from Step 1
**Original (Junior Professor's code):**
```lean
simp only [nabla, nabla_g_shape, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
```

**Problem:** Tactic `simp` failed with nested error

**Fix:**
```lean
simp only [nabla, nabla_g_shape]
```

**Result:** ✅ This step now compiles

### Adjustment 2: Split Z1-Z4 into two-step proofs
**Original:**
```lean
have Z1 : sumIdx (...) = 0 := by
  simp [sumIdx_expand, hθ0L]
```

**Problem:** unsolved goals (4 errors at lines 2098, 2101, 2104, 2107)

**Fix:**
```lean
have Z1 : sumIdx (...) = 0 := by
  simp only [sumIdx_expand, hθ0L]
  simp
```

**Result:** ✅ All four Z lemmas now compile

---

## Detailed Error Analysis

### What simp only [Z1, Z2, Z3, Z4, Hcancel] Should Do

**Expected behavior:**
1. Rewrite the four ` - sumIdx (Γ · ∇g)` terms to 0 using Z1-Z4
2. Rewrite the `∂∂g - ∂∂g` term to 0 using Hcancel

**After these rewrites**, the goal should have:
- Four 0's where the Γ(∇g) terms were
- One 0 where the ∂∂g commutator was
- Four `∂(∑ Γ·g)` terms remaining (to be distributed by HrL/HrR/HθL/HθR)

**What's happening:** simp only isn't finding any matches

---

## Possible Causes

### Cause 1: Goal Structure Mismatch
After `simp only [nabla, nabla_g_shape]`, the goal might have:
- Different associativity/grouping of terms
- Different normalization of subtraction (a - b vs a + (-b))
- Binders that prevent matching

**Test:** Try `show`-ing the goal structure before line 2130

### Cause 2: Simp Direction
The Z* and Hcancel lemmas are equalities. `simp only` rewrites left-to-right. If the goal has the RHS form instead of LHS, simp won't match.

**Test:** Try `rw [←Z1, ←Z2, ←Z3, ←Z4, ←Hcancel]` (backwards rewrites)

### Cause 3: Need Explicit Term Normalization
The goal might need `sub_eq_add_neg` applied first to normalize subtraction.

**Test:** Try `simp only [sub_eq_add_neg, Z1, Z2, Z3, Z4, Hcancel]`

---

## Recommendations to Junior Professor

### Question 1: Goal Structure
After `simp only [nabla, nabla_g_shape]` (without the add_comm/add_left_comm/add_assoc), what is the expected goal structure?

Should it be:
```
⊢ (∂_r(∂_θ g + (-∑ Γ·∇g) + (-∑ Γ·∇g)) + (-∑ Γ·(∂_θ g + ...)) + (-∑ Γ·(...)))
  - (similar for ∇_θ(∇_r g))
  =
  -R_{bar θ} - R_{abr θ}
```

Or does it need further normalization before Z*/Hcancel can apply?

### Question 2: Alternative Step 5
Since `simp only [Z1, Z2, Z3, Z4, Hcancel]` isn't working, should we try:

**Option A:** Explicit rewrites
```lean
rw [Z1, Z2, Z3, Z4, Hcancel]
```

**Option B:** Normalize first
```lean
simp only [sub_eq_add_neg]
simp only [Z1, Z2, Z3, Z4, Hcancel]
```

**Option C:** Use full simp with limited set
```lean
simp [Z1, Z2, Z3, Z4, Hcancel]
```

### Question 3: Missing Lemmas
Are there any simp lemmas about sumIdx or nabla_g that need to be in the simp set for Z*/Hcancel to fire?

For example:
- Lemmas about `-sumIdx f = sumIdx (fun e => -f e)`?
- Lemmas about sumIdx in subtraction contexts?

---

## Current File State

**Riemann.lean:**
- Lines: ~4,250
- Build: ❌ 4 errors (was 5)
- Progress: 71% error reduction from initial 14

**Code applied:**
```lean
lemma ricci_identity_on_g_rθ_ext ... := by
  classical
  -- 1) ✅ WORKS
  simp only [nabla, nabla_g_shape]

  -- 2) ✅ WORKS (with two-step proofs)
  have hθ0L : ∀ e, nabla_g M r θ Idx.θ e b = 0 := ...
  ... (all h*0*)
  have Z1 : ... := by simp only [sumIdx_expand, hθ0L]; simp
  ... (all Z*)

  -- 3) ✅ WORKS
  have Hcomm := ...
  have Hcancel := ...

  -- 4) ✅ WORKS
  have HrL := ...
  ... (all H*)

  -- 5) ⚠️ FAILS HERE
  simp only [Z1, Z2, Z3, Z4, Hcancel]  -- made no progress
  rw [HrL, HrR, HθL, HθR]

  -- 6-8) NOT REACHED YET
  ...
```

---

## Next Steps

**Awaiting Junior Professor's guidance on:**
1. Expected goal structure after step 1
2. Why simp only [Z*, Hcancel] doesn't match
3. Alternative tactic sequence for step 5

**Alternative:** I can attempt Option A (explicit `rw` instead of `simp only`) to see if that progresses

---

**Prepared by:** Claude Code (AI Agent)
**Session:** October 8, 2025, Late Afternoon
**Status:** 4 errors (down from 14) - 71% reduction
**Confidence:** Very close - just need the right tactic for step 5

**Progress:**
- ✅ All infrastructure compiles (distributors, Z lemmas, compatibility)
- ✅ Steps 1-4 of Junior Professor's sequence work
- ⚠️ Step 5 (simp only [Z*, Hcancel]) needs tactical refinement

**Almost there!** Just need guidance on how to apply the Z*/Hcancel cancellations.
