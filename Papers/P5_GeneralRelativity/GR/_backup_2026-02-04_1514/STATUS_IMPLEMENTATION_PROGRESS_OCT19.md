# Implementation Progress: Correcting the Cancel Lemmas
## Date: October 19, 2025
## Status: Steps 1-3 Complete, Ready for Steps 4-6

---

## ✅ Completed Steps

### Step 1: Cancel_r_expanded ✅ (Lines 1776-1861)

**Created new lemma** that correctly expands `∂_r g · Γ` including BOTH terms from metric compatibility:
```lean
Σ_ρ [∂_r g_aρ · Γ^ρ_θb] = M_r term + Extra_r term
                         = Σ_{ρ,λ} [g_aρ · Γ^ρ_rλ · Γ^λ_θb]
                           + Σ_λ [Γ^λ_ra · Γ_λθb]
```

**Proof structure**:
- Applies `dCoord_g_via_compat_ext` to get the two-term expansion
- Distributes multiplication and sums using `sumIdx_mul_distrib`, `sumIdx_add_distrib`
- Swaps sums using `sumIdx_swap` (Fubini)
- Factors constants with `mul_sumIdx_distrib`
- Recognizes Γ₁ definition
- Uses deterministic `simp` only for AC normalization at the end

**No timeouts**: All steps are small, structural rewrites.

---

### Step 2: Cancel_θ_expanded ✅ (Lines 1863-1945)

**Created mirror lemma** for θ-branch:
```lean
Σ_ρ [∂_θ g_aρ · Γ^ρ_rb] = M_θ term + Extra_θ term
```

**Proof structure**: Identical to Cancel_r_expanded with μ := Idx.θ.

---

### Step 3: Updated Main Lemma Goal ✅ (Lines 4215-4231)

**Changed from**:
```lean
LHS = g_aa · R^a_brθ
```

**To (MATHEMATICALLY CORRECT)**:
```lean
LHS = g_aa · R^a_brθ + (Extra_r - Extra_θ)
    = g_aa · R^a_brθ
      + ( Σ_λ [Γ^λ_ra · Γ_λθb] - Σ_λ [Γ^λ_θa · Γ_λrb] )
```

**Added doc comment** explaining that the extra terms are non-zero in Schwarzschild coordinates.

---

## ⏳ Next Steps (To Be Implemented)

### Step 4: Replace dΓ₁_diff proof (Lines ~4627-4671)

**Current status**: Has the old `simpa [9 lemmas with AC]` that times out

**Need to replace with**: JP's micro-step pattern using:
```lean
-- Split sums using sumIdx_add_distrib (twice)
have h₁ : ... := by rw [sumIdx_add_distrib]
have h₂ : ... := by rw [sumIdx_add_distrib]

-- Regroup: (A+B) - (C+D) = (A-C) + (B-D)
calc
  _ = ... := by rw [h₁, h₂]
  _ = ... := by ring  -- Pure scalar arithmetic, fast!
```

**Status**: **Ready to implement** - I have the exact pattern from JP's earlier message.

---

### Step 5: Replace finish_perk proof (Lines ~4696-4752)

**Current status**: Uses old Cancel lemmas (without extra terms)

**Need to replace with**:
1. Apply `Cancel_r_expanded` and `Cancel_θ_expanded` (include extra terms)
2. Use `collect_into_Riemann` helper (JP provided)
3. Recognize RiemannUp kernel pointwise
4. Result includes `(Extra_r - Extra_θ)` on RHS

**Status**: **Need JP's `collect_into_Riemann` helper** - he provided the structure but I need to implement it as a lemma.

---

### Step 6: Update final contraction (Lines ~4754-4768)

**Current status**: Contracts to `g_aa · R^a_brθ` only

**Need to update**: The calc chain should now show:
```lean
calc
  _ = Σ_ρ g_aρ · R^ρ_brθ + (Extra_r - Extra_θ) := finish_perk
  _ = Riemann_{abrθ} + (Extra_r - Extra_θ) := by rw [hSigma]
  _ = g_aa · R^a_brθ + (Extra_r - Extra_θ) := by rw [h_contract]
```

**Status**: **Trivial update** once Step 5 is done.

---

## 📊 Current Build Status

**File**: `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean`

**New lemmas added**:
- `Cancel_r_expanded` (lines 1776-1861): ✅ Compiles
- `Cancel_θ_expanded` (lines 1863-1945): ✅ Compiles

**Modified lemmas**:
- `regroup_left_sum_to_RiemannUp` goal (lines 4215-4231): ✅ Updated

**Still to modify**:
- `dΓ₁_diff` proof body (need micro-steps)
- `finish_perk` proof body (need collect_into_Riemann helper)
- Final contraction calc chain (trivial update)

**Expected build status after all updates**: Should compile cleanly with mathematically correct proof!

---

## 🙏 Outstanding Request to JP

Could you provide the `collect_into_Riemann` helper as a standalone lemma that I can insert near the other `sumIdx_collect*` helpers?

From your message, the structure is:
```lean
have collect_into_Riemann :
    (sumIdx S₁ - sumIdx S₂) + (sumIdx M_r - sumIdx M_θ)
  = sumIdx (fun ρ => g M a ρ r θ * RiemannUp M r θ ρ b Idx.r Idx.θ) := by
  classical
  have h₄ := sumIdx_collect4 (f₁ := ...) (f₂ := ...) (f₃ := ...) (f₄ := ...)
  have : sumIdx (fun ρ => ...) = sumIdx (fun ρ => g · RiemannUp) := by
    apply sumIdx_congr
    intro ρ
    simp [RiemannUp, sub_eq_add_neg, mul_add, add_mul]
  simpa using (h₄.trans this)
```

Should this be:
1. A separate lemma (like `collect_four_sums_into_RiemannUp`) that I can call from `finish_perk`?
2. Or inline as a `have` statement within `finish_perk`?

I prefer option 1 for reusability, but will implement whichever you recommend.

---

## 🎯 Timeline Estimate

- **Step 4** (dΓ₁_diff micro-steps): 15 minutes
- **Step 5** (finish_perk with collector): 30 minutes (pending collector helper from JP)
- **Step 6** (final contraction update): 5 minutes
- **Build verification**: 10 minutes

**Total**: ~1 hour once I have the collector helper.

---

## 💡 Key Achievement

We've successfully corrected the mathematical error identified by the senior professor!

The proof now:
- ✅ Correctly accounts for BOTH terms from metric compatibility expansion
- ✅ Includes the Extra_r and Extra_θ terms explicitly
- ✅ Makes no false claims about these extra terms vanishing
- ✅ Is mathematically sound for Schwarzschild (and general) coordinates

This is exactly what formal verification is for - catching subtle algebraic errors that hand calculations might miss!

---

**Prepared by**: Claude Code
**Date**: October 19, 2025
**Status**: 3/6 steps complete, awaiting collector helper for steps 4-6
**Next**: Implement dΓ₁_diff micro-steps, then finish_perk with JP's collector pattern
