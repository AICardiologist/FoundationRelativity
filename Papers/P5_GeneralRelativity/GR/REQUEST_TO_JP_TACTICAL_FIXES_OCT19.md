# Request to JP: Tactical Fixes for Cancel Lemmas
## Date: October 19, 2025
## Status: 4/6 Tasks Complete, Need Tactical Fixes for Lines 2677, 2693, 2702-2703

---

## ✅ What's Working

JP, I've successfully implemented 4 of your 6 tasks:

1. ✅ **Task 1**: Removed misplaced Cancel lemmas from lines 1776-1945
2. ✅ **Task 2**: Inserted Cancel lemmas after line 2633 (after `dCoord_g_via_compat_ext`)
3. ✅ **Task 3**: Replaced `dΓ₁_diff` with micro-steps - **compiles cleanly!**
   - Uses only `rw [sumIdx_add_distrib]` and `ring`
   - No timeouts, no AC lemmas
4. ✅ **Task 4**: Replaced `finish_perk` with `sumIdx_collect4` structure

The mathematical structure is correct - we're now properly including both M and Extra terms!

---

## ❌ What's Blocking

The **Cancel lemma proof bodies** have tactical errors at 3 specific locations. The calc proof steps are failing with errors I can't resolve.

---

## 🔴 ERROR 1: Line 2677 (Cancel_r_expanded)

### Location
```lean
lemma Cancel_r_expanded
    (M r θ : ℝ) (h_ext : Exterior M r θ) (a b : Idx) :
  sumIdx (fun ρ =>
    dCoord Idx.r (fun r θ => g M a ρ r θ) r θ * Γtot M r θ ρ Idx.θ b)
  =
  sumIdx (fun ρ =>
    g M a ρ r θ * sumIdx (fun lam =>
      Γtot M r θ ρ Idx.r lam * Γtot M r θ lam Idx.θ b))
  + sumIdx (fun lam =>
      Γtot M r θ lam Idx.r a * Γ₁ M r θ lam Idx.θ b) := by
  classical
  have compat_r :
      (fun ρ => dCoord Idx.r (fun r θ => g M a ρ r θ) r θ)
    = (fun ρ =>
        sumIdx (fun σ => Γtot M r θ σ Idx.r a * g M σ ρ r θ)
      + sumIdx (fun σ => Γtot M r θ σ Idx.r ρ * g M a σ r θ)) := by
    funext ρ
    exact dCoord_g_via_compat_ext M r θ h_ext Idx.r a ρ
  calc
    sumIdx (fun ρ =>
      dCoord Idx.r (fun r θ => g M a ρ r θ) r θ * Γtot M r θ ρ Idx.θ b)
        = sumIdx (fun ρ =>
            (sumIdx (fun σ => Γtot M r θ σ Idx.r a * g M σ ρ r θ)
           + sumIdx (fun σ => Γtot M r θ σ Idx.r ρ * g M a σ r θ))
            * Γtot M r θ ρ Idx.θ b) := by
              conv_lhs => arg 1; intro ρ; rw [dCoord_g_via_compat_ext M r θ h_ext Idx.r a ρ]
    _ = sumIdx (fun ρ =>
            (sumIdx (fun σ => Γtot M r θ σ Idx.r a * g M σ ρ r θ))
              * Γtot M r θ ρ Idx.θ b)
        + sumIdx (fun ρ =>
            (sumIdx (fun σ => Γtot M r θ σ Idx.r ρ * g M a σ r θ))
              * Γtot M r θ ρ Idx.θ b) := by
              rw [← sumIdx_add_distrib]; apply sumIdx_congr; intro ρ; ring
    _ = sumIdx (fun ρ =>
            sumIdx (fun σ =>
              Γtot M r θ σ Idx.r a * g M σ ρ r θ * Γtot M r θ ρ Idx.θ b))
        + sumIdx (fun ρ =>
            sumIdx (fun σ =>
              Γtot M r θ σ Idx.r ρ * g M a σ r θ * Γtot M r θ ρ Idx.θ b)) := by
              -- ❌ ERROR ON NEXT LINE (2677):
              congr 1 <;> (apply sumIdx_congr; intro ρ; rw [sumIdx_mul_distrib]; apply sumIdx_congr; intro σ; ring)
```

### Error Message
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:2677:81: No goals to be solved
```

### What I Think is Happening
The nested `sumIdx_congr` with binder shadowing (both outer and inner use `ρ`) combined with `rw [sumIdx_mul_distrib]` is confusing the elaborator.

### What I Need
The corrected tactic sequence for line 2677 that distributes `Γtot M r θ ρ Idx.θ b` through the inner `sumIdx`.

---

## 🔴 ERROR 2: Line 2693 (Cancel_r_expanded)

### Context (continuing the same calc chain)
```lean
    _ = sumIdx (fun σ =>
            sumIdx (fun ρ =>
              Γtot M r θ σ Idx.r a * g M σ ρ r θ * Γtot M r θ ρ Idx.θ b))
        + sumIdx (fun σ =>
            sumIdx (fun ρ =>
              Γtot M r θ σ Idx.r ρ * g M a σ r θ * Γtot M r θ ρ Idx.θ b)) := by
              congr 1 <;> rw [sumIdx_swap]
    _ = sumIdx (fun σ =>
            Γtot M r θ σ Idx.r a
              * sumIdx (fun ρ =>
                  g M σ ρ r θ * Γtot M r θ ρ Idx.θ b))
        + sumIdx (fun σ =>
            g M a σ r θ
              * sumIdx (fun ρ =>
                  Γtot M r θ σ Idx.r ρ * Γtot M r θ ρ Idx.θ b)) := by
              -- ❌ ERROR ON NEXT LINE (2693):
              congr 1 <;> (apply sumIdx_congr; intro σ; rw [← mul_sumIdx_distrib]; apply sumIdx_congr; intro ρ; ring)
```

### Error Message
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:2693:60: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  sumIdx fun k => ?c * ?f k
in the target expression
  (sumIdx fun ρ => Γtot M r θ σ Idx.r a * g M σ ρ r θ * Γtot M r θ ρ Idx.θ b) =
    Γtot M r θ σ Idx.r a * sumIdx fun ρ => g M σ ρ r θ * Γtot M r θ ρ Idx.θ b
```

### What I Think is Happening
The pattern `?c * sumIdx (fun k => ?f k)` in `mul_sumIdx_distrib` isn't matching because there are three multiplicands, not two. Needs reassociation or a different lemma.

### What I Need
The corrected tactic sequence for line 2693 that factors `Γtot M r θ σ Idx.r a` out of the sum.

---

## 🔴 ERROR 3: Lines 2702-2703 (Cancel_r_expanded)

### Context (final steps of the calc chain)
```lean
    _ = sumIdx (fun lam =>
            Γtot M r θ lam Idx.r a * Γ₁ M r θ lam Idx.θ b)
        + sumIdx (fun ρ =>
            g M a ρ r θ
              * sumIdx (fun lam =>
                  Γtot M r θ ρ Idx.r lam * Γtot M r θ lam Idx.θ b)) := by
              rw [add_comm]
              congr 1
              -- ❌ ERROR ON NEXT LINE (2702):
              · apply sumIdx_congr; intro σ; rw [Γ₁]; ring
              -- ❌ ERROR ON NEXT LINE (2703):
              · rfl
    _ = sumIdx (fun ρ =>
            g M a ρ r θ * sumIdx (fun lam =>
              Γtot M r θ ρ Idx.r lam * Γtot M r θ lam Idx.θ b))
        + sumIdx (fun lam =>
            Γtot M r θ lam Idx.r a * Γ₁ M r θ lam Idx.θ b) := by ring
```

### Error Messages
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:2702:14: unsolved goals
case e_a.h
M r θ : ℝ
h_ext : Exterior M r θ
a b : Idx
compat_r : ...
⊢ (sumIdx fun σ => Γtot M r θ σ Idx.r a * sumIdx fun ρ => g M σ ρ r θ * Γtot M r θ ρ Idx.θ b) =
  sumIdx fun lam => Γtot M r θ lam Idx.r a * Γ₁ M r θ lam Idx.θ b

error: Papers/P5_GeneralRelativity/GR/Riemann.lean:2703:16: Tactic `rfl` failed
```

### What I Think is Happening
Line 2702: The `rw [Γ₁]` is trying to unfold `Γ₁ M r θ lam Idx.θ b = sumIdx (fun ρ => g M lam ρ r θ * Γtot M r θ ρ Idx.θ b)`, but the binder names don't match (σ vs lam).

Line 2703: The second branch of `congr 1` is expecting reflexivity, but the terms aren't syntactically identical.

### What I Need
The corrected tactic sequence for lines 2702-2703 that:
1. Recognizes the Γ₁ definition inside the sum
2. Handles the dummy variable renaming (σ → lam)
3. Proves the second branch

---

## 🔴 DUPLICATE ERRORS: Cancel_θ_expanded

The **exact same three errors** appear in `Cancel_θ_expanded`:
- Line 2751: Same as error 1 (No goals to be solved)
- Line 2767: Same as error 2 (Tactic `rewrite` failed)
- Lines 2776-2777: Same as error 3 (unsolved goals / rfl failed)

Whatever fix works for `Cancel_r_expanded` will work for `Cancel_θ_expanded` with `Idx.r` → `Idx.θ`.

---

## 🙏 Request

Could you provide the **exact tactic sequences** to replace:

1. **Line 2677**: `congr 1 <;> (apply sumIdx_congr; intro ρ; rw [sumIdx_mul_distrib]; apply sumIdx_congr; intro σ; ring)`

2. **Line 2693**: `congr 1 <;> (apply sumIdx_congr; intro σ; rw [← mul_sumIdx_distrib]; apply sumIdx_congr; intro ρ; ring)`

3. **Lines 2702-2703**:
   ```lean
   · apply sumIdx_congr; intro σ; rw [Γ₁]; ring
   · rfl
   ```

Once these three fixes are applied to `Cancel_r_expanded`, I'll apply the same pattern to `Cancel_θ_expanded` and we should have a clean build!

---

## 📋 Alternative: Simplify with Sorry?

If debugging these tactics is too time-consuming, I could temporarily replace the Cancel lemma proof bodies with:

```lean
lemma Cancel_r_expanded ... := by sorry
lemma Cancel_θ_expanded ... := by sorry
```

This would let us **test whether the overall structure** (dΓ₁_diff + finish_perk + main lemma goal) is correct before polishing the Cancel lemma proofs.

Would you prefer I do this first to validate the architecture, or should I wait for the tactical fixes?

---

## 🎯 Bottom Line

**We're 95% there!** The mathematical structure is correct, dΓ₁_diff compiles cleanly, and finish_perk is structurally sound. We just need these three tactical fixes to get a clean build.

Thank you for your help!

---

**Prepared by**: Claude Code (quantmann)
**Date**: October 19, 2025
**Files**: `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean`
**Build log**: `/tmp/riemann_build.log`
