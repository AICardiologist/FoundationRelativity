# JP's Drop-In Proofs Attempt - October 26, 2025

**Date**: October 26, 2025
**Agent**: Claude Code (Sonnet 4.5)
**Status**: ⚠️ **Partial Success - First Proof Applied, Second Proof Needs Clarification**

---

## TL;DR

✅ **Proof #1 Applied**: `sum_k_prod_rule_to_Γ₁` - JP's complete proof integrated (lines 10950-11035)
❓ **Proof #2 Blocked**: `regroup_right_sum_to_Riemann_CORRECT` - Index mismatch, needs clarification

---

## What Was Attempted

### Proof #1: `sum_k_prod_rule_to_Γ₁` (Lines 10942-11035) ✅

**Goal**: Prove
```lean
sumIdx (fun k =>
  dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a * g M k b r θ) r θ
- dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a * g M k b r θ) r θ)
=
dCoord Idx.r (fun r θ => Γ₁ M r θ b a Idx.θ) r θ
- dCoord Idx.θ (fun r θ => Γ₁ M r θ b a Idx.r) r θ
```

**Solution Applied**: JP's complete 5-step proof

**Key Infrastructure Used** (all exist):
- `dCoord_sumIdx` (line 1185) - Interchange derivative and finite sum
- `differentiableAt_Γtot_all_r` (line 827) - Γ differentiability in r
- `differentiableAt_Γtot_all_θ` (line 855) - Γ differentiability in θ
- `differentiableAt_g_all_r` (line 512) - metric differentiability in r
- `differentiableAt_g_all_θ` (line 528) - metric differentiability in θ
- `sumIdx_map_sub` (line 1549) - Sum distributes over subtraction
- `DifferentiableAt.mul` (Mathlib) - Product differentiability

**Proof Structure**:
1. **Step 1**: Linearize outer Σ into difference of two Σs (using `sumIdx_map_sub`)
2. **Step 2**: Interchange ∂_r with Σ_k (using `dCoord_sumIdx`)
   - Prove differentiability conditions for Fθ = `Γ·g`
3. **Step 3**: Interchange ∂_θ with Σ_k (using `dCoord_sumIdx`)
   - Prove differentiability conditions for Fr = `Γ·g`
4. **Step 4**: Identify sums with Γ₁ definition
   - Use `Γtot_symmetry` and `g_symm_JP`
5. **Step 5**: Assemble calc chain

**Status**: ✅ **Proof complete** (pending build verification)

---

### Proof #2: `regroup_right_sum_to_Riemann_CORRECT` (Lines 11045-11071) ❓

**Goal**: Prove
```lean
sumIdx (fun k =>
  dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a * g M k b r θ) r θ
- dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a * g M k b r θ) r θ)
= sumIdx (fun k =>
    Riemann M r θ k a Idx.r Idx.θ * g M k b r θ)
```

**JP's Suggested Approach**:
1. Apply `sum_k_prod_rule_to_Γ₁` to get: `∂_r(Γ₁_{baθ}) - ∂_θ(Γ₁_{bar})`
2. Apply `Riemann_via_Γ₁.symm` to transform to: `Σ_k Riemann_{karθ} * g_{kb}`

**Problem Encountered**: Index mismatch in Step 2

**Analysis**:

From `sum_k_prod_rule_to_Γ₁`, we have (Step 1 ✅):
```
LHS = ∂_r(Γ₁_{baθ}) - ∂_θ(Γ₁_{bar})
```

From `Riemann_via_Γ₁` (line 2516), signature:
```lean
lemma Riemann_via_Γ₁ (M r θ : ℝ) (h_ext : Exterior M r θ) (h_θ : Real.sin θ ≠ 0) (β a : Idx) :
  Riemann M r θ β a Idx.r Idx.θ
  = dCoord Idx.r (fun r θ => Γ₁ M r θ β a Idx.θ) r θ
  - dCoord Idx.θ (fun r θ => Γ₁ M r θ β a Idx.r) r θ
  + sumIdx (fun lam => ...)  -- Extra term
```

**Issue**: We need to show:
```
∂_r(Γ₁_{baθ}) - ∂_θ(Γ₁_{bar}) = Σ_k Riemann_{karθ} * g_{kb}
```

But `Riemann_via_Γ₁` with β=b gives:
```
Riemann_{barθ} = ∂_r(Γ₁_{baθ}) - ∂_θ(Γ₁_{bar}) + extra_term
```

And by the definition of Riemann (line 4321):
```
Riemann_{barθ} = Σ_μ g_{bμ} · RiemannUp^μ_{arθ}
```

**Index Mismatch**:
- **Need**: `Σ_k Riemann_{karθ} * g_{kb}` (sum over **first index** of Riemann)
- **Have**: `Riemann_{barθ} = Σ_μ g_{bμ} · RiemannUp^μ_{arθ}` (Riemann with **first index fixed at b**)

**Possible Resolutions**:
1. **Missing lemma**: There may be a swap/symmetry lemma that relates these two forms
2. **Diagonality simplification**: For diagonal metrics, the sum might collapse differently
3. **Misunderstanding**: JP's proof may have used different index conventions
4. **Extra term**: The `extra_term` in `Riemann_via_Γ₁` might resolve the mismatch

**Status**: ⚠️ **Blocked - needs clarification from JP or user**

---

## Infrastructure Verification

All lemmas JP referenced exist in the codebase:

| Lemma | Line | Status |
|-------|------|--------|
| `dCoord_sumIdx` | 1185 | ✅ Exists |
| `differentiableAt_Γtot_all_r` | 827 | ✅ Exists |
| `differentiableAt_Γtot_all_θ` | 855 | ✅ Exists |
| `differentiableAt_g_all_r` | 512 | ✅ Exists |
| `differentiableAt_g_all_θ` | 528 | ✅ Exists |
| `DifferentiableAt_r_mul_of_cond` | 881 | ✅ Exists |
| `DifferentiableAt_θ_mul_of_cond` | 895 | ✅ Exists |
| `sumIdx_map_sub` | 1549 | ✅ Exists |
| `Riemann_via_Γ₁` | 2516 | ✅ Exists |
| `sum_RUp_g_to_Riemann_ba` | 4327 | ✅ Exists |
| `Γtot_symmetry` | - | ✅ Exists |
| `g_symm_JP` | - | ✅ Exists |

**My Initial Error**: I thought `dCoord_sumIdx_comm` didn't exist, but it's actually named `dCoord_sumIdx` ✅

---

## What Changed in Riemann.lean

### Lines 10950-11035 (Proof #1)

**Before** (my incomplete attempt):
```lean
:= by
  -- Direct proof: show the sums are equal pointwise, then apply dCoord
  -- Step 1: Unfold Γ₁ and recognize the sum structure
  have hr_eq : ∀ r' θ', sumIdx (fun k => Γtot M r' θ' k Idx.θ a * g M k b r' θ')
                        = Γ₁ M r' θ' b a Idx.θ := by
    intro r' θ'
    unfold Γ₁
    apply sumIdx_congr
    intro k
    rw [Γtot_symmetry, g_symm_JP]

  have hθ_eq : ∀ r' θ', sumIdx (fun k => Γtot M r' θ' k Idx.r a * g M k b r' θ')
                        = Γ₁ M r' θ' b a Idx.r := by
    intro r' θ'
    unfold Γ₁
    apply sumIdx_congr
    intro k
    rw [Γtot_symmetry, g_symm_JP]

  -- Step 2: Use function extensionality to rewrite the dCoord arguments
  have : (fun r θ => sumIdx (fun k => Γtot M r θ k Idx.θ a * g M k b r θ))
       = (fun r θ => Γ₁ M r θ b a Idx.θ) := by
    funext r' θ'; exact hr_eq r' θ'

  have : (fun r θ => sumIdx (fun k => Γtot M r θ k Idx.r a * g M k b r θ))
       = (fun r θ => Γ₁ M r θ b a Idx.r) := by
    funext r' θ'; exact hθ_eq r' θ'

  -- Step 3: Apply linearity of dCoord over sums and use the equalities
  sorry -- This needs the interchange lemma for finite sums with derivatives
```

**After** (JP's complete proof):
```lean
:= by
  classical
  -- Abbreviate the two families we differentiate/sum over
  set Fθ : Idx → ℝ → ℝ → ℝ :=
    (fun k r θ => Γtot M r θ k Idx.θ a * g M k b r θ)
  set Fr : Idx → ℝ → ℝ → ℝ :=
    (fun k r θ => Γtot M r θ k Idx.r a * g M k b r θ)

  -- Step 1: linearize the outer Σ into a difference of two Σs
  have split :
    sumIdx (fun k =>
      dCoord Idx.r (fun r θ => Fθ k r θ) r θ
      - dCoord Idx.θ (fun r θ => Fr k r θ) r θ)
    =
    sumIdx (fun k => dCoord Idx.r (fun r θ => Fθ k r θ) r θ)
    - sumIdx (fun k => dCoord Idx.θ (fun r θ => Fr k r θ) r θ) := by
    simpa using
      (sumIdx_map_sub
        (fun k => dCoord Idx.r (fun r θ => Fθ k r θ) r θ)
        (fun k => dCoord Idx.θ (fun r θ => Fr k r θ) r θ))

  -- Step 2: interchange dCoord_r with Σ_k (uses dCoord_sumIdx)
  have hFθ_r :
    ∀ k, DifferentiableAt_r (fun r θ => Fθ k r θ) r θ ∨ Idx.r ≠ Idx.r := by
    intro k; left
    have hΓ := differentiableAt_Γtot_all_r M r θ h_ext k Idx.θ a
    have hg  := differentiableAt_g_all_r     M r θ h_ext k b
    simpa [DifferentiableAt_r, Fθ] using (DifferentiableAt.mul hΓ hg)
  have hFθ_θ :
    ∀ k, DifferentiableAt_θ (fun r θ => Fθ k r θ) r θ ∨ Idx.r ≠ Idx.θ := by
    intro _; right; simp

  have swap_r :
    sumIdx (fun k => dCoord Idx.r (fun r θ => Fθ k r θ) r θ)
      = dCoord Idx.r (fun r θ => sumIdx (fun k => Fθ k r θ)) r θ := by
    simpa using
      (dCoord_sumIdx Idx.r (fun k => Fθ k) r θ hFθ_r hFθ_θ).symm

  -- Step 3: interchange dCoord_θ with Σ_k
  have hFr_r :
    ∀ k, DifferentiableAt_r (fun r θ => Fr k r θ) r θ ∨ Idx.θ ≠ Idx.r := by
    intro _; right; simp
  have hFr_θ :
    ∀ k, DifferentiableAt_θ (fun r θ => Fr k r θ) r θ ∨ Idx.θ ≠ Idx.θ := by
    intro k; left
    have hΓ := differentiableAt_Γtot_all_θ M r θ k Idx.r a (by exact h_ext.hθ_nonzero)
    have hg  := differentiableAt_g_all_θ     M r θ k b
    simpa [DifferentiableAt_θ, Fr] using (DifferentiableAt.mul hΓ hg)

  have swap_θ :
    sumIdx (fun k => dCoord Idx.θ (fun r θ => Fr k r θ) r θ)
      = dCoord Idx.θ (fun r θ => sumIdx (fun k => Fr k r θ)) r θ := by
    simpa using
      (dCoord_sumIdx Idx.θ (fun k => Fr k) r θ hFr_r hFr_θ).symm

  -- Step 4: identify the sums with Γ₁
  have eq_Γ₁_r : ∀ r' θ', sumIdx (fun k => Fθ k r' θ') = Γ₁ M r' θ' b a Idx.θ := by
    intro r' θ'
    unfold Γ₁ Fθ
    apply sumIdx_congr; intro k
    rw [Γtot_symmetry, g_symm_JP]
  have eq_Γ₁_θ : ∀ r' θ', sumIdx (fun k => Fr k r' θ') = Γ₁ M r' θ' b a Idx.r := by
    intro r' θ'
    unfold Γ₁ Fr
    apply sumIdx_congr; intro k
    rw [Γtot_symmetry, g_symm_JP]

  -- Step 5: assemble the calc chain
  calc
    sumIdx (fun k =>
      dCoord Idx.r (fun r θ => Fθ k r θ) r θ
      - dCoord Idx.θ (fun r θ => Fr k r θ) r θ)
      = sumIdx (fun k => dCoord Idx.r (fun r θ => Fθ k r θ) r θ)
        - sumIdx (fun k => dCoord Idx.θ (fun r θ => Fr k r θ) r θ) := split
    _ = dCoord Idx.r (fun r θ => sumIdx (fun k => Fθ k r θ)) r θ
        - dCoord Idx.θ (fun r θ => sumIdx (fun k => Fr k r θ)) r θ := by
          rw [swap_r, swap_θ]
    _ = dCoord Idx.r (fun r θ => Γ₁ M r θ b a Idx.θ) r θ
        - dCoord Idx.θ (fun r θ => Γ₁ M r θ b a Idx.r) r θ := by
          have : (fun r θ => sumIdx (fun k => Fθ k r θ)) = (fun r θ => Γ₁ M r θ b a Idx.θ) := by
            funext r' θ'; exact eq_Γ₁_r r' θ'
          have : (fun r θ => sumIdx (fun k => Fr k r θ)) = (fun r θ => Γ₁ M r θ b a Idx.r) := by
            funext r' θ'; exact eq_Γ₁_θ r' θ'
          simp [*]
```

**Net change**: +85 lines, -1 sorry ✅

### Lines 11052-11071 (Proof #2)

**Before**:
```lean
:= by
  -- This is a clean 3-step proof once Phases 1-3 are complete:
  -- Step 1: Apply sum_k_prod_rule_to_Γ₁ (Phase 2B)
  -- Step 2: Apply Riemann_via_Γ₁ (Phase 3) in reverse
  -- Step 3: Simplify

  -- TODO: Implement once Phase 2B and Phase 3 are filled in
  -- The structure should be:
  -- calc
  --   sumIdx (fun k => ∂_r(Γ·g) - ∂_θ(Γ·g))
  --   _ = sumIdx (fun k => ∂_r(Γ₁) - ∂_θ(Γ₁))  := sum_k_prod_rule_to_Γ₁
  --   _ = sumIdx (fun k => Riemann * g)          := Riemann_via_Γ₁.symm
  sorry
```

**After** (partial attempt):
```lean
:= by
  classical
  -- Step 1: Apply sum_k_prod_rule_to_Γ₁ to collapse the sum
  have H := sum_k_prod_rule_to_Γ₁ M r θ h_ext a b

  -- Step 2: Recognize that Γ₁ derivatives equal summed Riemann form
  -- We need: dCoord_r(Γ₁_{baθ}) - dCoord_θ(Γ₁_{bar}) = Σ_k Riemann_{karθ} * g_{kb}
  -- By definition of Riemann: Riemann_{barθ} = Σ_k g_{bk} · RiemannUp^k_{arθ}
  -- And by Riemann_via_Γ₁: Riemann_{barθ} relates to Γ₁ derivatives

  calc
    sumIdx (fun k =>
      dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a * g M k b r θ) r θ
      - dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a * g M k b r θ) r θ)
        = dCoord Idx.r (fun r θ => Γ₁ M r θ b a Idx.θ) r θ
          - dCoord Idx.θ (fun r θ => Γ₁ M r θ b a Idx.r) r θ := H
    _   = sumIdx (fun k => Riemann M r θ k a Idx.r Idx.θ * g M k b r θ) := by
            -- This step uses the relationship between Γ₁ and Riemann
            -- For now, apply the pattern JP suggested
            sorry
```

**Net change**: +20 lines, -0 sorrys (still 1 sorry remaining)

---

## Build Status

⏳ **Pending**: Build currently running to verify Proof #1

**Expected outcome**:
- ✅ Proof #1 should compile successfully
- ⚠️ Proof #2 still has `sorry` due to index mismatch

---

## Questions for JP / User

1. **Index Convention**: In `regroup_right_sum_to_Riemann_CORRECT`, the RHS is:
   ```
   sumIdx (fun k => Riemann M r θ k a Idx.r Idx.θ * g M k b r θ)
   ```
   This sums over the **first index** of Riemann. Is there a lemma that relates this to the standard Riemann definition (line 4321) which has:
   ```
   Riemann_{abcd} = Σ_μ g_{aμ} · RiemannUp^μ_{bcd}
   ```

2. **Riemann_via_Γ₁ Extra Term**: The `Riemann_via_Γ₁` lemma has an extra `sumIdx (fun lam => ...)` term. Does this cancel when we form the sum `Σ_k Riemann_{karθ} * g_{kb}`?

3. **Missing Lemma**: Is there a lemma like:
   ```lean
   lemma sum_Riemann_first_index_eq_Γ₁ (M r θ : ℝ) (a b : Idx) :
     sumIdx (fun k => Riemann M r θ k a Idx.r Idx.θ * g M k b r θ)
     = dCoord Idx.r (fun r θ => Γ₁ M r θ b a Idx.θ) r θ
       - dCoord Idx.θ (fun r θ => Γ₁ M r θ b a Idx.r) r θ
   ```

---

## Recommendation

1. **Proof #1**: ✅ **Complete** - awaiting build verification
2. **Proof #2**: ⚠️ **Needs JP clarification** on index mismatch

**Action Items**:
- Wait for build to complete
- If Proof #1 compiles successfully, update documentation
- Ask JP for clarification on Proof #2 indices
- Once clarified, complete Proof #2

**Alternative**: If Proof #2 is truly blocked, document this as the final remaining `sorry` (non-critical, Phase 2B-3 infrastructure bypassed by Option C)

---

**Prepared By**: Claude Code (Sonnet 4.5)
**Date**: October 26, 2025
**Status**: ⚠️ **Partial Success (1/2 Proofs Applied)**

---
