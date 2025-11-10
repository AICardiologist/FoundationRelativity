# Critical Report to JP: Paul's Surgical Fixes Failed - November 2, 2025

**Date**: November 2, 2025
**Agent**: Claude Code (Lean 4 Assistant)
**Build**: `build_paul_surgical_fixes_nov2.txt`
**Total Errors**: 17 (unchanged from baseline)
**Infrastructure Errors**: 2 (lines 1745, 1759) - **STILL FAILING**
**Status**: 🔴 **CRITICAL FAILURE** - Definitional unfolding issue persists

---

## Executive Summary

Paul's surgical fixes were **correctly applied** to both infrastructure lemmas (`insert_delta_right_diag` and `insert_delta_left_diag`), but they **failed to resolve the definitional unfolding issue**. The same error persists: `simpa` unfolds `g` to a match expression before applying the hypothesis `hz`, making the hypothesis unusable.

**Key Finding**: The "pinned identity + simpa transport" pattern does NOT avoid the definitional unfolding problem in this context. The transport mechanism itself triggers the unfolding.

---

## What Was Applied

### Paul's Surgical Fix Pattern

Both infrastructure lemmas now use Paul's recommended pattern:

```lean
·
  have hz : g M ρ b r θ = 0 := g_offdiag_zero M r θ h
  -- Reduce to a pure 0=0 identity, then transport back with hz and if_neg h.
  have : F ρ * 0 = F ρ * 0 * 0 := by simp
  simpa [hz, if_neg h] using this
```

**Verification**: Lines 1745-1749 (`insert_delta_right_diag`) and lines 1759-1765 (`insert_delta_left_diag`) in `Riemann.lean`

---

## Build Results

### Full Fresh Compilation

**Build Command**: `lake build Papers.P5_GeneralRelativity.GR.Riemann`
**Compilation**: ✅ Riemann.lean was actually compiled (48 seconds)
**Exit Code**: 0 (syntactically valid)
**Total Errors**: 17

### Error Breakdown

**Infrastructure Errors (2)**:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:1745:2: unsolved goals
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:1759:2: unsolved goals
```

**Block A Cascade Errors (2)**:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8731:76: unexpected token 'have'; expected 'lemma'
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8946:75: unexpected token 'have'; expected 'lemma'
```

**Other Pre-existing Errors (13)**: Lines 2339, 3075, 6047, 7499, 7801, 8603, 8068, 9360, 9426, 9493, 9531

---

## Critical Error Analysis: Line 1745

### Full Error Message

```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:1745:2: unsolved goals
case neg
M r θ : ℝ
b : Idx
F : Idx → ℝ
ρ : Idx
h : ¬ρ = b
hz : g M ρ b r θ = 0
⊢ F ρ = 0 ∨
    (match (motive := Idx → Idx → ℝ → ℝ → ℝ) ρ, b with
        | t, t => fun r _θ => -f M r
        | Idx.r, Idx.r => fun r _θ => (f M r)⁻¹
        | Idx.θ, Idx.θ => fun r _θ => r ^ 2
        | φ, φ => fun r θ => r ^ 2 * sin θ ^ 2
        | x, x_1 => fun x x => 0)
        r θ =
      0
warning: Papers/P5_GeneralRelativity/GR/Riemann.lean:1747:10: This simp argument is unused:
  hz

Hint: Omit it from the simp argument list.
```

### Root Cause

**The definitional unfolding happens DURING `simpa` transport**, not before:

1. ✅ `have : F ρ * 0 = F ρ * 0 * 0 := by simp` - **This works fine**
2. ❌ `simpa [hz, if_neg h] using this` - **This triggers definitional unfolding**

**Why**: When `simpa` tries to transport `this` back to the goal, it:
1. Unfolds the goal to attempt matching
2. Unfolds `g M ρ b r θ` to the match expression shown above
3. Can no longer recognize `g M ρ b r θ` to apply `hz`
4. Warning: "This simp argument is unused: hz"

### Expected vs Actual Goal State

**Expected Goal** (what Paul's fix should produce):
```lean
⊢ F ρ * g M ρ b r θ = F ρ * g M ρ b r θ * (if ρ = b then 1 else 0)
```

**Actual Goal State** (after definitional unfolding):
```lean
⊢ F ρ = 0 ∨ (match ρ, b with | t, t => fun r _θ => -f M r | ...) r θ = 0
```

The goal has been **rewritten into a disjunction** where `g` is completely unfolded, making `hz : g M ρ b r θ = 0` unmatchable.

---

## Why Paul's Fix Didn't Work

### The Pinned Identity Approach

Paul's strategy was:
1. Prove a simple numeric fact: `F ρ * 0 = F ρ * 0 * 0` (works)
2. Transport it back using `simpa [hz, if_neg h]` (fails)

**Problem**: The transport mechanism (`simpa using this`) requires Lean to:
- Match `this` (a `0 = 0` identity) against the actual goal
- Substitute `0` back to `g M ρ b r θ` and `if ρ = b then 1 else 0`
- But during this matching, Lean unfolds `g` definitionally

**Result**: The unfolding happens INSIDE the `simpa` tactic, not in the goal state beforehand. This means Paul's approach of "pinning the shape" doesn't prevent the unfolding during transport.

### Comparison to Paul's Explanation

Paul said:
> "Fix: don't try to rewrite the actual goal directly. First prove the purely numeric equation with literal zeros, and then simpa back to your goal using [hz, if_neg h]. That pins the shape and avoids any reliance on whether g is folded or unfolded."

**Reality**: The transport via `simpa using this` STILL relies on whether `g` is folded or unfolded, because Lean unfolds during the backward matching process.

---

## What This Means

### Key Insight

**The definitional unfolding issue is more fundamental than expected**. It's not just about the order of rewrites or whether we prove the simplified case first - it's that **any tactic that needs to match against the goal will trigger definitional unfolding of `g`**.

### Tactics That Don't Work

1. ❌ `simp [hz, if_neg h]` - unfolds `g` before applying `hz`
2. ❌ `have : ... := by simp; simpa [hz, if_neg h] using this` - unfolds `g` during transport
3. ❌ Direct rewrites with `g` in the goal

### What We Need

A tactic strategy that:
- Never needs to match the current goal state containing `g M ρ b r θ`
- OR forces `g` to remain folded during all unification
- OR manually constructs the proof term without relying on unification

---

## Evidence: Current File State

### insert_delta_right_diag (lines 1737-1749)

```lean
lemma insert_delta_right_diag (M r θ : ℝ) (b : Idx) (F : Idx → ℝ) :
  sumIdx (fun ρ => F ρ * g M ρ b r θ)
    =
  sumIdx (fun ρ => F ρ * g M ρ b r θ * (if ρ = b then 1 else 0)) := by
  classical
  refine sumIdx_congr (fun ρ => ?_)
  by_cases h : ρ = b
  · subst h; simp
  ·
    have hz : g M ρ b r θ = 0 := g_offdiag_zero M r θ h
    -- Reduce to a pure 0=0 identity, then transport back with hz and if_neg h.
    have : F ρ * 0 = F ρ * 0 * 0 := by simp
    simpa [hz, if_neg h] using this  -- ❌ FAILS HERE (line 1749)
```

### insert_delta_left_diag (lines 1753-1765)

```lean
lemma insert_delta_left_diag (M r θ : ℝ) (a : Idx) (F : Idx → ℝ) :
  sumIdx (fun ρ => g M a ρ r θ * F ρ)
    =
  sumIdx (fun ρ => g M a ρ r θ * F ρ * (if ρ = a then 1 else 0)) := by
  classical
  refine sumIdx_congr (fun ρ => ?_)
  by_cases h : ρ = a
  · subst h; simp
  ·
    have hz : g M a ρ r θ = 0 := g_offdiag_zero M r θ (ne_comm.mpr h)
    -- Again, argue via a pinned 0=0 identity.
    have : 0 * F ρ = 0 * F ρ * 0 := by simp
    simpa [hz, if_neg h] using this  -- ❌ FAILS HERE (line 1765)
```

---

## Questions for JP

### Q1: Alternative Tactic Strategies

Are there tactics that can:
1. Force `g` to remain folded during unification?
2. Build the proof term directly without `simp`/`simpa`?
3. Use `convert` with explicit unification hints?

### Q2: Why Does `simpa using` Trigger Unfolding?

Is there a way to control the unification depth or prevent definitional unfolding during the `simpa using` transport?

### Q3: Should We Use `conv` Mode?

Can we use `conv` mode to rewrite specific subexpressions without triggering full goal unification?

Example:
```lean
conv_lhs =>
  arg 1
  rw [hz]
conv_rhs =>
  arg 1
  arg 1
  rw [hz]
-- Then close with ring
```

### Q4: Manual Proof Term Construction?

Should we abandon tactic mode entirely for these lemmas and write the proof term directly?

---

## Cascade Effects

### Block A Still Broken

The Block A errors at lines 8731 and 8946 ("unexpected token 'have'; expected 'lemma'") are **cascade errors** from the infrastructure lemma failures. Once `insert_delta_right_diag` and `insert_delta_left_diag` compile, these should disappear.

**Evidence**: These errors are NOT in the infrastructure section (lines 1700-1800) but in Block A (lines 8640-9100), and are parse errors caused by the proof context being malformed due to upstream failures.

---

## Next Steps Required

### Immediate

1. **Consult JP**: What tactic strategy can avoid the definitional unfolding during unification/transport?
2. **Test alternatives**: Try `conv` mode, `convert`, or manual proof term construction
3. **Document findings**: This is a fundamental limitation of the `simpa using` approach

### Medium-Term

Once we find a working tactic strategy:
1. Apply to both infrastructure lemmas
2. Verify they compile
3. Check that Block A cascade errors disappear
4. Measure total error reduction

---

## Build File Location

**Full build output**: `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/build_paul_surgical_fixes_nov2.txt`

**Key sections**:
- Infrastructure error at line 1745: Lines 1-20 of grep output
- Infrastructure error at line 1759: Similar pattern
- Block A cascade errors: Lines 8731, 8946

---

**Prepared by**: Claude Code (Lean 4 Assistant)
**For**: JP (Junior Professor / Tactic Expert)
**CC**: Paul (Senior Professor)
**Date**: November 2, 2025
**Status**: Awaiting tactical guidance - definitional unfolding blocker persists

---

**END OF CRITICAL REPORT**
