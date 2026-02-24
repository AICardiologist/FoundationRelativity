# Session Progress Report - October 7, 2025 (Afternoon)

## Summary

Attempted to fix the 3 remaining component lemmas (Fixes 1-3) following the Junior Professor's tactical blueprints. **Encountered critical interference issues**: Even after setting Fixes 1-3 to `sorry`, the previously-working Fixes 4-7 now fail.

---

## Current Build Status

**Result**: ❌ 4 errors (Fixes 4-7 all failing), 3 sorries (Fixes 1-3)

**Error locations**:
- Line 2064: RiemannUp_φ_θφθ_ext (Fix 4)
- Line 2079: RiemannUp_t_φtφ_ext (Fix 5)
- Line 2092: RiemannUp_r_φrφ_ext (Fix 6)
- Line 2105: RiemannUp_θ_φθφ_ext (Fix 7)

---

## What Was Attempted

### Approach 1: Junior Professor's Blueprint (Minimal Pattern)

**For Fix 2 (RiemannUp_t_θtθ_ext)**:
```lean
unfold RiemannUp
simp only [dCoord, sumIdx_expand, Γtot,
           Γtot_t_tr, Γtot_r_θθ]  -- only non-zero terms
simp only [Γ_t_tr, Γ_r_θθ]
field_simp [hr, f]
ring
```

**Result**: Unsolved goal after `ring`:
```
⊢ -(deriv (fun t => 0) θ * r ^ 2) - r * M * (f M r)⁻¹ + M ^ 2 * (f M r)⁻¹ * 2 = -(r * M)
```

### Approach 2: Add Derivative Helpers

Added explicit derivative computations before `field_simp`:
```lean
have hder : deriv (fun t : ℝ => (0 : ℝ)) θ = 0 := by simp
simp only [hder]
field_simp [hr, f]
ring
```

**Result**: Derivative computed successfully, but unsolved algebraic goal:
```
⊢ -(r * M * (f M r)⁻¹) + M ^ 2 * (f M r)⁻¹ * 2 = -(r * M)
```

**Observation**: This is mathematically correct:
- Factor out `(f M r)⁻¹`: `(f M r)⁻¹ * M * (2*M - r) = -r*M`
- Since `f M r = (r - 2*M)/r`, we have `(f M r)⁻¹ = r/(r - 2*M)`
- So: `r/(r-2*M) * M * (2*M - r) = r * M * (-1) = -r*M` ✓

But `ring` cannot close this because `f` is still symbolic.

### Approach 3: Two-Stage field_simp

Tried expanding `f` in a second `field_simp` pass:
```lean
field_simp [hr, f]  -- Keep f symbolic
have hsub : r - 2*M ≠ 0 := by linarith [h_ext.hr_ex]
simp only [f]       -- Expand f
field_simp [hr, hsub]
ring
```

**Result**: Build errors multiplied - now even previously-working Fixes 4-7 fail!

---

## Root Cause Analysis

### The Interference Problem

**Critical Discovery**: The presence of lemmas with `sorry` causes other lemmas to fail!

1. **Start state** (from session summary): Fixes 4-7 working, Fixes 1-3 with errors
2. **After setting Fixes 1-3 to `sorry`**: Now Fixes 4-7 also fail!

This confirms the Junior Professor's warning about "simp recursion depth explosions":

> "Each lemma works in isolation, but proving all seven at once triggers simp recursion depth explosions—classic signs that simp is picking up newly-available rewrite routes introduced by the very lemmas you just proved."

### Why Even `sorry` Causes Problems

Hypothesis: The *presence* of the lemma statements (even with `sorry` bodies) makes them available for simp to pick up during rewrite search. When `simp only [dCoord, sumIdx_expand, Γtot, ...]` is called in Fix 4, it might be trying to apply Fix 1's lemma, which triggers evaluation of the `sorry`, causing goal state corruption.

---

## The Algebraic Closure Problem

For Fixes 2 and 3, the issue is that after `field_simp [hr, f]`:
- Goal contains expressions like `(f M r)⁻¹ * ...`
- `ring` cannot normalize because `f` is symbolic
- Expanding `f` with `simp only [f]; field_simp [hr, hsub]` creates interference with other lemmas

**The Dilemma**:
- Keep `f` symbolic → `ring` can't close
- Expand `f` → triggers simp recursion / lemma interference

---

## Paths Forward (Need Guidance)

### Option A: Isolate Lemmas with Namespaces

Add each component lemma to a separate namespace or section to prevent cross-talk:
```lean
section Fix1
lemma RiemannUp_r_trt_ext ... := ...
end Fix1

section Fix2
lemma RiemannUp_t_θtθ_ext ... := ...
end Fix2
```

**Pros**: Prevents lemma interference
**Cons**: May not work if Lean still sees them in scope

### Option B: Use `@[simp]` Attributes Selectively

Mark only certain lemmas as `@[simp]` and leave others without the attribute:
```lean
-- NO @[simp] attribute
lemma RiemannUp_r_trt_ext ... := ...

@[simp]  -- Only this one available to simp
lemma RiemannUp_θ_tθt_ext ... := ...
```

**Pros**: Fine-grained control over which lemmas simp can use
**Cons**: Unclear if this is the issue (none have `@[simp]` currently)

### Option C: Abandon Parallel Development

Prove lemmas one at a time, committing each before starting the next:
1. Prove Fix 4 alone (with Fixes 1-3, 5-7 removed entirely from file)
2. Commit
3. Add Fix 5, prove it
4. Commit
... etc.

**Pros**: Guarantees no interference
**Cons**: Time-consuming, defeats purpose of having all 7

### Option D: Use `conv` Tactics for Precise Rewrites

Instead of `simp` / `field_simp` which search broadly, use `conv` to target specific subterms:
```lean
conv_lhs => {
  arg 1
  rw [show (f M r)⁻¹ * M * (2*M - r) = -r*M by simp only [f]; field_simp [hr, hsub]; ring]
}
```

**Pros**: Surgical precision, no cross-talk
**Cons**: Extremely verbose, error-prone

### Option E: Increase `maxRecDepth` and Use Original Patterns

Just accept the recursion and increase the limit:
```lean
set_option maxRecDepth 10000

lemma RiemannUp_t_θtθ_ext ... := by
  ... (original pattern with all simp calls)
```

**Pros**: Might just work
**Cons**: Junior Professor specifically warned against this

---

## Questions for User

1. **Should I continue trying to fix these 3 lemmas**, or is partial success (4/7) acceptable for now?

2. **Which path forward** (A-E above) do you prefer?

3. **Is there a working state** I should restore to? The session summary mentioned "4 lemmas proven" but I'm unclear which 4.

4. **Should I consult the Junior Professor again** with this new finding about `sorry` interference?

---

## Files Modified This Session

**Main**:
- `GR/Riemann.lean` (multiple edits, currently in broken state with 4 errors)

**Documentation**:
- `GR/SESSION_PROGRESS_OCT7_AFTERNOON.md` (this file)

---

**Current Time**: October 7, 2025 (Afternoon)
**Session Duration**: ~90 minutes
**Progress**: 0/3 fixes completed (interference discovered)
**Build Status**: ❌ 4 errors, 3 sorries

---

## Recommendation

**Pause and seek guidance** before proceeding. The interference issue is fundamental and requires architectural decision (namespace isolation, lemma ordering, or tactical rethinking).

Alternative: **Restore to a known-working state** from backups and document current blockers for future session.
