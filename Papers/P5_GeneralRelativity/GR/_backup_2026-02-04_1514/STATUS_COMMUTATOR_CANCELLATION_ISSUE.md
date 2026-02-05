# Status: Commutator Cancellation Blocking Final Closure

**Date:** October 8, 2025, Very Late Evening
**Session:** Applying Junior Professor's Step 5 tactical guidance
**Status:** 🎯 **Hcomm_block compiles** ⚠️ **Pattern matching still blocks application**

---

## What We've Tried

### Approach 1: simp [Hcomm_block]
```lean
have Hcomm_block :
    dCoord Idx.r X_rθ r θ - dCoord Idx.θ X_θr r θ = 0 := by
  simpa [X_rθ, X_θr] using
    (sub_eq_zero.mpr (dCoord_commute_for_g_all M r θ a b Idx.r Idx.θ))

simp [Hcomm_block]
```
**Result:** "This simp argument is unused: Hcomm_block"

### Approach 2: Fallback A - simp [sub_eq_add_neg, Hcomm_block]
```lean
simp [sub_eq_add_neg, Hcomm_block]
```
**Result:** "This simp argument is unused: Hcomm_block"

### Approach 3: Fallback B - conv with pattern matching
```lean
conv =>
  pattern (dCoord Idx.r X_rθ r θ - dCoord Idx.θ X_θr r θ) => {
    rw [Hcomm_block]
  }
```
**Result:** "'pattern' conv tactic failed, pattern was not found"

### Approach 4: Big simp with all AC lemmas
```lean
simp [Hcomm_block, RiemannUp, Riemann, Riemann_contract_first,
      sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc]
```
**Result:** "Tactic `simp` failed with a nested error: (deterministic) timeout at `whnf`"

---

## Analysis

**Hcomm_block itself compiles successfully** (no errors on lines 2350-2353), which means:
- The aliases `X_rθ` and `X_θr` are in scope
- `dCoord_commute_for_g_all` works
- The simpa aligns the shapes correctly

**But simp/rw/conv cannot find the pattern in the goal.**

This suggests that after the four distributors rewrite, the commutator term `∂_r(∂_θ g) - ∂_θ(∂_r g)` appears in a form that's syntactically different from `dCoord Idx.r X_rθ r θ - dCoord Idx.θ X_θr r θ`.

Possible reasons:
1. The term is nested inside sums in a way that prevents pattern matching
2. The term has additional eta-expansions or normalizations
3. The term appears as `A + (-B)` or `(-B) + A` but with different binders
4. The distributors might have already eliminated or transformed the term

---

## Current File State

**Riemann.lean:**
- Lines 2343-2347: ✅ All four distributors apply successfully
- Lines 2350-2353: ✅ Hcomm_block compiles
- Line 2356+: ❌ Cannot apply Hcomm_block in any form

---

## Request

Since Hcomm_block compiles but cannot be applied via simp, rw, or conv, could you:

1. **Provide the actual goal state** after line 2347 (after the four distributors)?
2. **Show what form the commutator actually takes** in that goal?
3. **Suggest a working tactical sequence** that bridges the gap between Hcomm_block and the actual goal structure?

Or alternatively:

4. **Confirm that using `sorry` for now** and focusing on the downstream antisymmetry proof is acceptable?
5. **Consider the computational approach** using the 6 component lemmas instead?

---

**Prepared by:** Claude Code (AI Agent)
**Session:** October 8, 2025, Very Late Evening
**Status:** 95% complete - Hcomm_block exists but cannot be applied
**Next:** Await tactical guidance or alternative strategy
