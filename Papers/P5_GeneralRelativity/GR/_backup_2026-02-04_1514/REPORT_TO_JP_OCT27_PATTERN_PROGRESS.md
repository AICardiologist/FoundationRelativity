# Report to JP: Pattern Implementation Progress (October 27, 2025)

**Agent**: Claude Code (Sonnet 4.5)
**Session Duration**: ~2 hours
**Starting Errors**: 32
**Current Errors**: 28
**Errors Fixed**: 4 (12.5% reduction)

---

## ✅ Success: Pattern A - Ring Inside Binder (4 errors fixed)

### Discovery: Your fold_sub_right Lemmas Don't Exist

JP, I discovered that the fold lemmas you referenced don't exist in this codebase:
- `fold_sub_right` - not found
- `fold_add_left` - not found
- `group_sub_add` - not found
- `group_add_sub` - not found

When I tried your full normalizer pattern, it failed with:
```
unknown identifier 'fold_sub_right'
```

### Working Solution Found

I developed a simpler pattern that achieves the same goal using standard Finset lemmas:

```lean
apply sumIdx_congr; intro e
simp only [sumIdx, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]
```

**Why this works**:
1. Unfolds `sumIdx` to `Finset.sum`
2. Applies `Finset.mul_sum` to factor constants: `∑ i, a * f i = a * ∑ i, f i`
3. Normalizes multiplication order with `mul_comm`, `mul_assoc`, `mul_left_comm`
4. Lean's congruence closure handles the rest

### Sites Successfully Fixed

**Line 7196-7198**:
```lean
_ = sumIdx (fun e => g M e b r θ * sumIdx (fun ρ =>
        Γtot M r θ ρ μ a * Γtot M r θ e ν ρ)) := by
  apply sumIdx_congr; intro e
  simp only [sumIdx, Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]
```

**Also applied at**: Lines 7221, 7370, 7392

### Verification

Build went from **32 → 28 errors**. All 4 Pattern A sites now compile successfully.

---

## ⚠️ Blocker: Pattern C - Rewrite Failures (3 sites)

### The Problem

Your Pattern C guidance was:
```lean
change
  sumIdx (fun ρ => (A ρ - B ρ) + (C ρ - D ρ)) = _
rw [sumIdx_add_distrib]
```

I applied `change` but the rewrite still fails. Here's a concrete example:

### Site 1: Line 7238-7240

**Current code**:
```lean
have first_block :
  sumIdx (fun ρ => sumIdx (fun e =>
    ((Γtot M r θ ρ μ a * Γtot M r θ e ν ρ)
   - (Γtot M r θ ρ ν a * Γtot M r θ e μ ρ)) * g M e b r θ))
  =
  g M b b r θ *
    ( sumIdx (fun ρ => Γtot M r θ ρ μ a * Γtot M r θ b ν ρ)
    - sumIdx (fun ρ => Γtot M r θ ρ ν a * Γtot M r θ b μ ρ) ) := by
  -- Use sub_congr with sumIdx_map_sub
  have h := sub_congr H₁ H₂
  change sumIdx (fun ρ => sumIdx (fun e =>
    ((Γtot M r θ ρ μ a * Γtot M r θ e ν ρ) - (Γtot M r θ ρ ν a * Γtot M r θ e μ ρ)) * g M e b r θ)) = _
  rw [← h, sumIdx_map_sub, sumIdx_map_sub]  -- ❌ FAILS HERE
  ring
```

**Error message**:
```
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  (g M b b r θ * sumIdx fun ρ => Γtot M r θ ρ μ a * Γtot M r θ b ν ρ) -
    g M b b r θ * sumIdx fun ρ => Γtot M r θ ρ ν a * Γtot M r θ b μ ρ
in the target expression
  (sumIdx fun ρ =>
      sumIdx fun e => (Γtot M r θ ρ μ a * Γtot M r θ e ν ρ - Γtot M r θ ρ ν a * Γtot M r θ e μ ρ) * g M e b r θ) =
    g M b b r θ *
      ((sumIdx fun ρ => Γtot M r θ ρ μ a * Γtot M r θ b ν ρ) - sumIdx fun ρ => Γtot M r θ ρ ν a * Γtot M r θ b μ ρ)
```

**Where `h` comes from**:
```lean
have H₁ : [complex calc chain proving first equality]
have H₂ : [complex calc chain proving second equality]
have h := sub_congr H₁ H₂
```

So `h` has type:
```
h : (LHS₁ = RHS₁) → (LHS₂ = RHS₂) → (LHS₁ - LHS₂ = RHS₁ - RHS₂)
```

### Why `rw [← h]` Fails

The issue is that after `change`, the goal is:
```
sumIdx (fun ρ => sumIdx (fun e => ...)) = g M b b r θ * (sumIdx ... - sumIdx ...)
```

But `h` wants to match the RHS pattern `(g M b b r θ * sumIdx ...) - (g M b b r θ * sumIdx ...)`, which is NOT the same as `g M b b r θ * (sumIdx ... - sumIdx ...)` due to the factored constant.

### Same Issue at 2 Other Sites

**Line 7788-7789**:
```lean
_   = - sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ)
    + rho_core_b := by
  simp only [h_rho_core_b]
  change _ = - sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ) + rho_core_b
  rw [← core_as_sum_b, ← sumIdx_add_distrib]  -- ❌ FAILS
```

**Line 7924-7925**: Same pattern, different variables (a/b swapped)

---

## 🤔 Questions for JP

### Q1: Are fold_sub_right lemmas supposed to exist?

Should I create these helper lemmas, or is there a different import I'm missing?

### Q2: Pattern C - How to make the rewrite match?

For the `first_block` example, do I need to:
1. **Option A**: First distribute `g M b b r θ` back into the subtraction before applying `h`?
2. **Option B**: Use a different lemma than `sub_congr` that works with factored forms?
3. **Option C**: Apply `sumIdx_map_sub` first, THEN the subtraction congruence?
4. **Option D**: Something else entirely?

### Q3: Is there a one-liner for this pattern?

Given:
- `H₁ : LHS₁ = RHS₁` (proven via calc chain)
- `H₂ : LHS₂ = RHS₂` (proven via calc chain)
- Goal: `sumIdx (fun ρ => sumIdx (fun e => (A - B) * C)) = factored_RHS`

What's the minimal tactic sequence?

---

## 📊 Full Error Breakdown (28 remaining)

### Category 1: Rewrite Failures (3) ⚠️ **BLOCKING**
- **7240**: `first_block` - described above
- **7789**: `rho_core_b` - sumIdx_add_distrib fails
- **7925**: `rho_core_a` - sumIdx_add_distrib fails

### Category 2: Type Mismatches (4) - Ready for Pattern B
- **7712, 7782, 7917**: `simpa only [payload_cancel, ΓΓ_block] using (sumIdx_congr scalar_finish)` fails
- **8367**: Type mismatch (different context)

### Category 3: "simp made no progress" (4) - Ready for Pattern D
- **8339, 8347, 8419, 8427**: Need `rfl` or `ring` instead of `simp`

### Category 4: Unsolved Goals (12) - Likely Cascading
- Lines: 7290, 7453, 7727, 7766, 7862, 7904, 7679, 7815, 7962, 8009, 8318, 8405
- These may auto-resolve when upstream errors fixed

### Category 5: Other (5)
- **7409, 7850**: Simp failed with nested error
- **7493**: Assumption failed (cascading)

---

## 🎯 Recommended Next Steps

### Option 1: You provide one-liners for Pattern C sites
Paste me the exact tactic sequence for line 7238-7240, and I'll mechanically apply to the other 2 sites.

### Option 2: I continue with Patterns B & D while waiting
- Pattern B: 4 type mismatches (your two-step pointwise approach)
- Pattern D: 4 "simp made no progress" (replace with direct closers)
- This could fix ~8 more errors, bringing us to ~20 total

### Option 3: Create the fold lemmas myself
If you tell me the expected signatures, I can add them to the helper lemma section.

---

## 📝 Files Modified This Session

**Riemann.lean**:
- Lines 7196-7198: Pattern A fix ✅
- Lines 7221: Pattern A fix ✅
- Lines 7238-7240: Pattern C attempted (blocked)
- Lines 7370: Pattern A fix ✅
- Lines 7392: Pattern A fix ✅
- Lines 7788-7789: Pattern C attempted (blocked)
- Lines 7924-7925: Pattern C attempted (blocked)

**Build logs**:
- `/tmp/build_simp_mul_sum.txt` - After Pattern A (28 errors)
- `/tmp/build_pattern_c.txt` - After Pattern C attempts (28 errors, no change)

---

## 💡 What I Learned

1. **Your codebase uses custom sumIdx, not Finset.sum exclusively**: So unfolding to Finset gives us access to standard library lemmas
2. **Finset.mul_sum is powerful**: It's the right tool for factoring constants out of sums
3. **`change` alone isn't sufficient**: Need to understand the full rewrite chain to match patterns correctly
4. **Multiplication normalization helps**: Adding `mul_comm, mul_assoc, mul_left_comm` to simp catches many edge cases

---

**Status**: Awaiting JP's guidance on Pattern C rewrite strategy.
**Confidence**: High on Patterns B & D; Blocked on Pattern C.
**Estimated time to 20 errors**: 1-2 hours if Pattern C gets unblocked.

---

**Prepared By**: Claude Code (Sonnet 4.5)
**For**: JP (Lean Tactics Professor)
**Date**: October 27, 2025
**Build Verification**: ✅ Compiles with 28 errors (down from 32)
