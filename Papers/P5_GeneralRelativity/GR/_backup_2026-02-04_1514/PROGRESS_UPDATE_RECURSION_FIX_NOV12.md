# Progress Update: Recursion Fixed, Need Guidance on Final Step - November 12, 2024

**Status**: ⚠️ **PARTIAL SUCCESS - Recursion resolved, final step needs revision**
**Error Count**: 18 errors (baseline) - **NO DEGRADATION** ✅
**For**: Paul
**From**: Claude Code

---

## Executive Summary

I resolved the recursion error at line 8990 by replacing `simpa` with `rw [hs]; ring`. This avoids the infinite rewrite loop with commutativity lemmas. However, the final collapse step at line 8994 now has a rewrite failure.

**Current state**: Lines 8985-8995 now compile partially, but need the correct finale for the δ-collapse.

---

## Changes Applied

### Line 8990: Recursion Fix ✅

**Original (caused recursion)**:
```lean
simpa [hs, neg_mul, mul_neg, mul_comm, mul_left_comm, mul_assoc]
```

**Fixed (no recursion)**:
```lean
rw [hs]
ring
```

**Result**: ✅ Line 8990 now compiles without recursion error.

---

### Line 8994: Still Failing ❌

**Current code**:
```lean
      have hswap_fun :
          (fun ρ => -(g M b ρ r θ * G ρ)) = (fun ρ => g M ρ b r θ * -(G ρ)) := by
        funext ρ
        have hs : g M b ρ r θ = g M ρ b r θ := g_swap_local M r θ b ρ
        -- Algebraic normalization with metric swap
        rw [hs]
        ring
      have hδ := insert_delta_right_of_commuted_neg M r θ b G
      -- Collapse the δ with the standard right-δ eliminator.
      rw [← hswap_fun]  -- ❌ THIS LINE FAILS
      exact hδ
```

**Error at line 8994**:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8994:10: Tactic `rewrite` failed: Did not find an occurrence of the pattern
```

---

## What Works Now

1. **Line 8990 (funext proof)**: ✅ `ring` successfully proves the pointwise equality after metric swap
2. **Line 8992 (δ-insertion)**: ✅ `have hδ := insert_delta_right_of_commuted_neg M r θ b G` compiles
3. **Error count**: Still 18 (same as baseline) - no new errors introduced

---

## What Needs Fixing

The final collapse step (lines 8993-8995) needs revision. Your original code was:

```lean
simpa [hswap_fun, sumIdx_delta_right] using hδ
```

I tried:
```lean
rw [← hswap_fun]
exact hδ
```

But the rewrite fails. The goal at this point probably doesn't match the pattern expected by `hswap_fun`.

---

## Request for Paul

**Option 1: Provide exact tactic for lines 8993-8995**

What should replace:
```lean
      -- Collapse the δ with the standard right-δ eliminator.
      rw [← hswap_fun]
      exact hδ
```

to correctly apply the δ-collapse?

**Option 2: Use simplified approach**

If `simpa [hswap_fun, sumIdx_delta_right] using hδ` is causing issues due to the simplifier, could we use:
- `simp only [hswap_fun, sumIdx_delta_right]` then `exact hδ`?
- Or `conv_lhs => ...` to manipulate the goal?
- Or a different approach altogether?

---

## Current Code (lines 8985-8995)

```lean
      have hswap_fun :
          (fun ρ => -(g M b ρ r θ * G ρ)) = (fun ρ => g M ρ b r θ * -(G ρ)) := by
        funext ρ
        have hs : g M b ρ r θ = g M ρ b r θ := g_swap_local M r θ b ρ
        -- Algebraic normalization with metric swap
        rw [hs]
        ring
      have hδ := insert_delta_right_of_commuted_neg M r θ b G
      -- Collapse the δ with the standard right-δ eliminator.
      rw [← hswap_fun]  -- ❌ FAILS HERE
      exact hδ
```

---

## What I Need

The exact replacement for lines 8993-8995 that will:
1. Use `hswap_fun` to rewrite the goal
2. Apply `hδ` with the δ-collapse lemma `sumIdx_delta_right`
3. Close the proof without recursion or rewrite failures

---

## Build Evidence

- **build_recursion_fix_nov12.txt**: Shows recursion error resolved at line 8990
- **build_ring_fix_nov12.txt**: Shows current state with line 8994 rewrite failure
- **Error count**: 18 (same as baseline)

---

## Summary

- ✅ **Recursion fixed**: Replaced `simpa` with `rw [hs]; ring` at line 8990
- ❌ **Final step needs revision**: Line 8994 rewrite fails
- ✅ **No degradation**: Still at 18 errors (baseline)
- ⏳ **Waiting for**: Paul's guidance on the correct finale (lines 8993-8995)

---

**Report Time**: November 12, 2024
**Key Achievement**: Recursion error eliminated
**Blocker**: Need correct δ-collapse tactic for line 8993-8995
