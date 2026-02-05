# Action Plan: Correct the Cancel Lemmas and Fix the Proof
## Date: October 19, 2025
## Based on: JP's guidance and Senior Professor's review

---

## 🎯 Summary of the Fix

**The Problem**: Our Cancel lemmas claimed:
```
Σ_ρ [∂_r g_aρ · Γ^ρ_θb] = Σ_{ρ,λ} [g_aρ · Γ^ρ_rλ · Γ^λ_θb]
```

**The Truth** (from metric compatibility):
```
Σ_ρ [∂_r g_aρ · Γ^ρ_θb] = Σ_{ρ,λ} [g_aρ · Γ^ρ_rλ · Γ^λ_θb] + Σ_λ [Γ^λ_ra · Γ_λθb]
                           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^   ^^^^^^^^^^^^^^^^^^^^
                           M_r term (we had this)             Extra_r term (MISSING!)
```

**The Fix**: Create new lemmas `Cancel_r_expanded` and `Cancel_θ_expanded` that include the extra terms explicitly.

---

## 📋 Step-by-Step Implementation Plan

### Step 1: Create Cancel_r_expanded (NEW LEMMA)

**Location**: Add after the existing `Riemann_via_Γ₁_Cancel_r` (around line 1775)

**Full lemma statement**:
```lean
/-- Correct expansion of the `(∂g)·Γ` block (r-branch) including the extra term. -/
lemma Cancel_r_expanded
    (M r θ : ℝ) (h_ext : Exterior M r θ) (a b : Idx) :
  -- LHS: (∂_r g)·Γ term
  sumIdx (fun ρ =>
    dCoord Idx.r (fun r θ => g M a ρ r θ) r θ * Γtot M r θ ρ Idx.θ b)
  =
  -- M_r term: what the old Cancel_r gave us
  sumIdx (fun ρ =>
    g M a ρ r θ * sumIdx (fun lam =>
      Γtot M r θ ρ Idx.r lam * Γtot M r θ lam Idx.θ b))
  -- + Extra_r term: the missing piece!
  + sumIdx (fun lam =>
      Γtot M r θ lam Idx.r a * Γ₁ M r θ lam Idx.θ b) := by
  classical
  -- Proof strategy (JP's outline):
  -- 1. Apply metric compatibility pointwise: dCoord_g_via_compat_ext
  -- 2. Multiply by Γ^ρ_θb and sum over ρ
  -- 3. Split into two terms using mul_sumIdx_distrib
  -- 4. First term → Σ_λ Γ^λ_ra · Γ₁_λθb (using Γ₁ definition)
  -- 5. Second term → Σ_ρ g_aρ · Σ_λ Γ^ρ_rλ · Γ^λ_θb (using sumIdx_mul_sumIdx_swap)
  -- 6. Regroup with ring on scalars
  sorry  -- Will implement with JP's detailed recipe
```

**Request to JP**: Could you provide the exact `calc` block / `rw` sequence for this proof? I have the helper lemmas:
- `dCoord_g_via_compat_ext` (line 2594)
- `mul_sumIdx_distrib`
- `sumIdx_mul_distrib`
- `sumIdx_mul_sumIdx_swap`
- `Γ₁` definition (line 1090)

### Step 2: Create Cancel_θ_expanded (NEW LEMMA)

**Location**: Add immediately after `Cancel_r_expanded`

**Full lemma statement**:
```lean
/-- Correct expansion of the `(∂g)·Γ` block (θ-branch) including the extra term. -/
lemma Cancel_θ_expanded
    (M r θ : ℝ) (h_ext : Exterior M r θ) (a b : Idx) :
  -- LHS: (∂_θ g)·Γ term
  sumIdx (fun ρ =>
    dCoord Idx.θ (fun r θ => g M a ρ r θ) r θ * Γtot M r θ ρ Idx.r b)
  =
  -- M_θ term
  sumIdx (fun ρ =>
    g M a ρ r θ * sumIdx (fun lam =>
      Γtot M r θ ρ Idx.θ lam * Γtot M r θ lam Idx.r b))
  -- + Extra_θ term
  + sumIdx (fun lam =>
      Γtot M r θ lam Idx.θ a * Γ₁ M r θ lam Idx.r b) := by
  classical
  -- Mirror of Cancel_r_expanded with μ := Idx.θ
  sorry  -- Will implement with JP's recipe
```

### Step 3: Update the Main Lemma Goal

**Location**: Line 4045-4054

**Current goal**:
```lean
lemma regroup_left_sum_to_RiemannUp
    (M r θ : ℝ) (h_ext : Exterior M r θ) (h_θ : Real.sin θ ≠ 0) (a b : Idx) :
  sumIdx (fun k => ...) = g M a a r θ * RiemannUp M r θ a b Idx.r Idx.θ
```

**New goal (with extra terms)**:
```lean
lemma regroup_left_sum_to_RiemannUp
    (M r θ : ℝ) (h_ext : Exterior M r θ) (h_θ : Real.sin θ ≠ 0) (a b : Idx) :
  sumIdx (fun k =>
      dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ b) r θ * g M a k r θ
    - dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r b) r θ * g M a k r θ
    + Γtot M r θ k Idx.θ b * dCoord Idx.r (fun r θ => g M a k r θ) r θ
    - Γtot M r θ k Idx.r b * dCoord Idx.θ (fun r θ => g M a k r θ) r θ)
  =
  g M a a r θ * RiemannUp M r θ a b Idx.r Idx.θ
  + ( sumIdx (fun lam =>
        Γtot M r θ lam Idx.r a * Γ₁ M r θ lam Idx.θ b)
    - sumIdx (fun lam =>
        Γtot M r θ lam Idx.θ a * Γ₁ M r θ lam Idx.r b) )
```

**This is now mathematically correct!**

### Step 4: Replace dΓ₁_diff proof with micro-steps

**Location**: Lines 4457-4501

**Current proof**: Uses `simpa [9 lemmas with AC] using this` → times out

**New proof** (JP's micro-step pattern):
```lean
have dΓ₁_diff :
    dCoord Idx.r (fun r θ => Γ₁ M r θ a Idx.θ b) r θ
  - dCoord Idx.θ (fun r θ => Γ₁ M r θ a Idx.r b) r θ
  =
    (sumIdx (fun ρ =>
        g M a ρ r θ * dCoord Idx.r (fun r θ => Γtot M r θ ρ Idx.θ b) r θ)
    - sumIdx (fun ρ =>
        g M a ρ r θ * dCoord Idx.θ (fun r θ => Γtot M r θ ρ Idx.r b) r θ))
  + (sumIdx (fun ρ =>
        dCoord Idx.r (fun r θ => g M a ρ r θ) r θ * Γtot M r θ ρ Idx.θ b)
    - sumIdx (fun ρ =>
        dCoord Idx.θ (fun r θ => g M a ρ r θ) r θ * Γtot M r θ ρ Idx.r b)) := by
  -- Deterministic rewrite: no AC simp
  rw [dΓ₁_r, dΓ₁_θ]

  -- Split sums using sumIdx_add_distrib (twice)
  have h₁ : sumIdx (fun ρ =>
      dCoord Idx.r (fun r θ => g M a ρ r θ) r θ * Γtot M r θ ρ Idx.θ b
    + g M a ρ r θ * dCoord Idx.r (fun r θ => Γtot M r θ ρ Idx.θ b) r θ)
    = sumIdx (fun ρ =>
        dCoord Idx.r (fun r θ => g M a ρ r θ) r θ * Γtot M r θ ρ Idx.θ b)
    + sumIdx (fun ρ =>
        g M a ρ r θ * dCoord Idx.r (fun r θ => Γtot M r θ ρ Idx.θ b) r θ) := by
    rw [sumIdx_add_distrib]

  have h₂ : sumIdx (fun ρ =>
      dCoord Idx.θ (fun r θ => g M a ρ r θ) r θ * Γtot M r θ ρ Idx.r b
    + g M a ρ r θ * dCoord Idx.θ (fun r θ => Γtot M r θ ρ Idx.r b) r θ)
    = sumIdx (fun ρ =>
        dCoord Idx.θ (fun r θ => g M a ρ r θ) r θ * Γtot M r θ ρ Idx.r b)
    + sumIdx (fun ρ =>
        g M a ρ r θ * dCoord Idx.θ (fun r θ => Γtot M r θ ρ Idx.r b) r θ) := by
    rw [sumIdx_add_distrib]

  -- Regroup: (A+B) - (C+D) = (A-C) + (B-D)
  calc
    _ = (sumIdx (fun ρ =>
          dCoord Idx.r (fun r θ => g M a ρ r θ) r θ * Γtot M r θ ρ Idx.θ b)
       + sumIdx (fun ρ =>
          g M a ρ r θ * dCoord Idx.r (fun r θ => Γtot M r θ ρ Idx.θ b) r θ))
      - (sumIdx (fun ρ =>
          dCoord Idx.θ (fun r θ => g M a ρ r θ) r θ * Γtot M r θ ρ Idx.r b)
       + sumIdx (fun ρ =>
          g M a ρ r θ * dCoord Idx.θ (fun r θ => Γtot M r θ ρ Idx.r b) r θ)) := by
      rw [h₁, h₂]
    _ = (sumIdx (fun ρ =>
          g M a ρ r θ * dCoord Idx.r (fun r θ => Γtot M r θ ρ Idx.θ b) r θ)
        - sumIdx (fun ρ =>
          g M a ρ r θ * dCoord Idx.θ (fun r θ => Γtot M r θ ρ Idx.r b) r θ))
      + (sumIdx (fun ρ =>
          dCoord Idx.r (fun r θ => g M a ρ r θ) r θ * Γtot M r θ ρ Idx.θ b)
        - sumIdx (fun ρ =>
          dCoord Idx.θ (fun r θ => g M a ρ r θ) r θ * Γtot M r θ ρ Idx.r b)) := by
      ring  -- Pure scalar arithmetic, fast!
```

**No AC lemmas, no simp search, deterministic!**

### Step 5: Replace finish_perk proof with expanded cancels

**Location**: Lines 4526-4582

**Key change**: Use `Cancel_r_expanded` and `Cancel_θ_expanded` instead of the old Cancel lemmas

**New structure**:
```lean
have finish_perk :
    (sumIdx (fun ρ =>
        g M a ρ r θ * dCoord Idx.r (fun r θ => Γtot M r θ ρ Idx.θ b) r θ)
    - sumIdx (fun ρ =>
        g M a ρ r θ * dCoord Idx.θ (fun r θ => Γtot M r θ ρ Idx.r b) r θ))
  + (sumIdx (fun ρ =>
        dCoord Idx.r (fun r θ => g M a ρ r θ) r θ * Γtot M r θ ρ Idx.θ b)
    - sumIdx (fun ρ =>
        dCoord Idx.θ (fun r θ => g M a ρ r θ) r θ * Γtot M r θ ρ Idx.r b))
  = sumIdx (fun ρ => g M a ρ r θ * RiemannUp M r θ ρ b Idx.r Idx.θ)
    + ( sumIdx (fun lam => Γtot M r θ lam Idx.r a * Γ₁ M r θ lam Idx.θ b)
      - sumIdx (fun lam => Γtot M r θ lam Idx.θ a * Γ₁ M r θ lam Idx.r b) ) := by
  classical
  -- Apply the expanded cancel lemmas (with extra terms)
  have h_r := Cancel_r_expanded M r θ h_ext a b
  have h_θ := Cancel_θ_expanded M r θ h_ext a b

  -- Substitute h_r and h_θ into the second block
  calc
    _ = (sumIdx (fun ρ =>
          g M a ρ r θ * dCoord Idx.r (fun r θ => Γtot M r θ ρ Idx.θ b) r θ)
        - sumIdx (fun ρ =>
          g M a ρ r θ * dCoord Idx.θ (fun r θ => Γtot M r θ ρ Idx.r b) r θ))
      + ( (sumIdx (fun ρ =>
            g M a ρ r θ * sumIdx (fun lam =>
              Γtot M r θ ρ Idx.r lam * Γtot M r θ lam Idx.θ b))
          + sumIdx (fun lam =>
            Γtot M r θ lam Idx.r a * Γ₁ M r θ lam Idx.θ b))
        - (sumIdx (fun ρ =>
            g M a ρ r θ * sumIdx (fun lam =>
              Γtot M r θ ρ Idx.θ lam * Γtot M r θ lam Idx.r b))
          + sumIdx (fun lam =>
            Γtot M r θ lam Idx.θ a * Γ₁ M r θ lam Idx.r b)) ) := by
      -- Apply h_r and h_θ via rw or congr_arg
      rw [h_r, h_θ]
    _ = ( (sumIdx (fun ρ =>
            g M a ρ r θ * dCoord Idx.r (fun r θ => Γtot M r θ ρ Idx.θ b) r θ)
          - sumIdx (fun ρ =>
            g M a ρ r θ * dCoord Idx.θ (fun r θ => Γtot M r θ ρ Idx.r b) r θ))
        + (sumIdx (fun ρ =>
            g M a ρ r θ * sumIdx (fun lam =>
              Γtot M r θ ρ Idx.r lam * Γtot M r θ lam Idx.θ b))
          - sumIdx (fun ρ =>
            g M a ρ r θ * sumIdx (fun lam =>
              Γtot M r θ ρ Idx.θ lam * Γtot M r θ lam Idx.r b))) )
      + ( sumIdx (fun lam => Γtot M r θ lam Idx.r a * Γ₁ M r θ lam Idx.θ b)
        - sumIdx (fun lam => Γtot M r θ lam Idx.θ a * Γ₁ M r θ lam Idx.r b) ) := by
      ring  -- Regroup at top level
    _ = sumIdx (fun ρ =>
          g M a ρ r θ * ( dCoord Idx.r (fun r θ => Γtot M r θ ρ Idx.θ b) r θ
                        - dCoord Idx.θ (fun r θ => Γtot M r θ ρ Idx.r b) r θ
                        + sumIdx (fun lam =>
                            Γtot M r θ ρ Idx.r lam * Γtot M r θ lam Idx.θ b)
                        - sumIdx (fun lam =>
                            Γtot M r θ ρ Idx.θ lam * Γtot M r θ lam Idx.r b) ))
      + ( sumIdx (fun lam => Γtot M r θ lam Idx.r a * Γ₁ M r θ lam Idx.θ b)
        - sumIdx (fun lam => Γtot M r θ lam Idx.θ a * Γ₁ M r θ lam Idx.r b) ) := by
      -- Collect into single sum (use sumIdx_collect4 or manual)
      sorry  -- Request JP's exact collector pattern
    _ = sumIdx (fun ρ => g M a ρ r θ * RiemannUp M r θ ρ b Idx.r Idx.θ)
      + ( sumIdx (fun lam => Γtot M r θ lam Idx.r a * Γ₁ M r θ lam Idx.θ b)
        - sumIdx (fun lam => Γtot M r θ lam Idx.θ a * Γ₁ M r θ lam Idx.r b) ) := by
      -- Recognize RiemannUp kernel pointwise
      apply sumIdx_congr
      intro ρ
      simp [RiemannUp]  -- Pure unfolding, cheap
```

### Step 6: Update the final contraction

**Location**: Lines 4583-4597

**Current**: Contracts to `g_aa · R^a_brθ`

**New**: Contracts to `g_aa · R^a_brθ + (Extra_r - Extra_θ)`

```lean
-- Identify the ρ-sum as Riemann and contract
have hSigma :
    sumIdx (fun ρ =>
      g M a ρ r θ * RiemannUp M r θ ρ b Idx.r Idx.θ)
  = Riemann M r θ a b Idx.r Idx.θ := by
  simp [Riemann]

have h_contract :
    Riemann M r θ a b Idx.r Idx.θ
  = g M a a r θ * RiemannUp M r θ a b Idx.r Idx.θ :=
  Riemann_contract_first M r θ a b Idx.r Idx.θ

-- Put all equalities together (now including extra terms)
calc
  _ = sumIdx (fun ρ => g M a ρ r θ * RiemannUp M r θ ρ b Idx.r Idx.θ)
    + ( sumIdx (fun lam => Γtot M r θ lam Idx.r a * Γ₁ M r θ lam Idx.θ b)
      - sumIdx (fun lam => Γtot M r θ lam Idx.θ a * Γ₁ M r θ lam Idx.r b) ) := finish_perk
  _ = Riemann M r θ a b Idx.r Idx.θ
    + ( sumIdx (fun lam => Γtot M r θ lam Idx.r a * Γ₁ M r θ lam Idx.θ b)
      - sumIdx (fun lam => Γtot M r θ lam Idx.θ a * Γ₁ M r θ lam Idx.r b) ) := by
    rw [hSigma]
  _ = g M a a r θ * RiemannUp M r θ a b Idx.r Idx.θ
    + ( sumIdx (fun lam => Γtot M r θ lam Idx.r a * Γ₁ M r θ lam Idx.θ b)
      - sumIdx (fun lam => Γtot M r θ lam Idx.θ a * Γ₁ M r θ lam Idx.r b) ) := by
    rw [h_contract]
```

---

## 🙏 Request to JP

Could you please provide the exact proof bodies for:

1. **Cancel_r_expanded** (the `sorry` in Step 1)
   - Specifically the `calc` block or `rw` sequence using:
     - `dCoord_g_via_compat_ext`
     - `mul_sumIdx_distrib`, `sumIdx_mul_distrib`
     - `sumIdx_mul_sumIdx_swap`
     - `Γ₁` definition
     - `ring` on scalars

2. **Cancel_θ_expanded** (the `sorry` in Step 2)
   - Can probably mirror Cancel_r_expanded with μ := Idx.θ

3. **The collector pattern** (the `sorry` in Step 5)
   - How to use `sumIdx_collect4` or manual collection to get from 4 separate sums to 1 sum with the RiemannUp kernel

I have all the helper lemmas in the codebase - I just need the exact sequence to apply them deterministically.

---

## ✅ Expected Outcome

After implementing all 6 steps:

1. ✅ **Mathematically correct**: Includes the extra (Γ·Γ₁) terms that don't vanish in Schwarzschild
2. ✅ **No timeouts**: All simp calls replaced with deterministic rewrites + ring
3. ✅ **Clean build**: Proof compiles successfully with correct mathematics
4. ✅ **Verifiable**: Can check that extra terms have the right sign and structure for Schwarzschild components

---

**Prepared by**: Claude Code
**Date**: October 19, 2025
**Status**: Ready to implement pending JP's detailed proof bodies
**Next**: Wait for JP's calc blocks, then execute Steps 1-6
