/-
Papers/P2_BidualGap/HB/DualIsometries.lean

Isometric identifications to discharge the two DualIsBanach axioms:
1. (c₀ →L[ℝ] ℝ) ≃ₗᵢ ℓ¹
2. (ℓ¹ →L[ℝ] ℝ) ≃ₗᵢ ℓ^∞

These will allow us to prove:
- WLPO → DualIsBanach c₀
- WLPO → DualIsBanach (c₀ →L[ℝ] ℝ)
-/

import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Papers.P2_BidualGap.Basic
import Papers.P2_BidualGap.HB.DirectDual

namespace Papers.P2.HB

open scoped BigOperators

/-
================================================================================
PART A: (c₀ →L[ℝ] ℝ) ≃ₗᵢ ℓ¹
================================================================================
-/

section C0DualIsoL1

/-- Extract coefficients from a continuous linear functional on c₀ -/
def toCoeffs : (c₀ →L[ℝ] ℝ) →ₗ[ℝ] (ℕ → ℝ) where
  toFun f := fun n => f (e n)
  map_add' := by
    -- TODO: Show (f + g)(e n) = f(e n) + g(e n)
    sorry
  map_smul' := by
    -- TODO: Show (r • f)(e n) = r • f(e n)
    sorry

/-- The coefficients are summable with ℓ¹ norm equal to operator norm -/
lemma toCoeffs_summable (f : c₀ →L[ℝ] ℝ) : 
    Summable (fun n => ‖f (e n)‖) := by
  -- TODO: Use the fact that for any finite F ⊆ ℕ,
  -- ∑_{n ∈ F} |f(e n)| ≤ ‖f‖ (via signVector test)
  -- This is already proven in DirectDual.lean
  sorry

/-- The coefficients satisfy ℓ¹ norm equals operator norm -/
lemma toCoeffs_norm_eq (f : c₀ →L[ℝ] ℝ) :
    ∑' n, ‖f (e n)‖ = ‖f‖ := by
  -- TODO: 
  -- 1. Show ≤ using finite sum bounds
  -- 2. Show ≥ by testing f on truncated sign vectors
  -- (Reuse signVector lemmas from DirectDual.lean)
  sorry

/-- toCoeffs lands in ℓ¹ -/
def toCoeffsL1 : (c₀ →L[ℝ] ℝ) →ₗᵢ[ℝ] ℓ¹ where
  toLinearMap := {
    toFun := fun f => ⟨toCoeffs f, by
      -- TODO: Show membership in ℓ¹
      -- Use toCoeffs_summable
      sorry⟩
    map_add' := by sorry
    map_smul' := by sorry
  }
  norm_map' := by
    -- TODO: Use toCoeffs_norm_eq
    sorry

/-- Reconstruct a functional from ℓ¹ coefficients -/
def ofCoeffs (a : ℓ¹) : c₀ →L[ℝ] ℝ where
  toLinearMap := {
    toFun := fun x => ∑' n, a.val n * x.val n
    map_add' := by
      -- TODO: Distributivity of infinite sum
      sorry
    map_smul' := by
      -- TODO: Scalar multiplication through infinite sum
      sorry
  }
  cont := by
    -- TODO: Show ‖ofCoeffs a‖ ≤ ‖a‖₁
    -- Use ∑ |aₙ xₙ| ≤ ‖a‖₁ ‖x‖∞
    sorry

/-- ofCoeffs has norm equal to ℓ¹ norm -/
lemma ofCoeffs_norm_eq (a : ℓ¹) :
    ‖ofCoeffs a‖ = ‖a‖ := by
  -- TODO:
  -- 1. ≤ direction: standard estimate
  -- 2. ≥ direction: test on sign vectors for a
  sorry

/-- The main isometry: c₀ dual ≃ ℓ¹ -/
def dual_c0_iso_l1 : (c₀ →L[ℝ] ℝ) ≃ₗᵢ[ℝ] ℓ¹ where
  toLinearEquiv := {
    toFun := toCoeffsL1.toLinearMap.toFun
    invFun := ofCoeffs
    left_inv := by
      -- TODO: Show ofCoeffs (toCoeffsL1 f) = f
      -- Key: f x = ∑' n, f(e n) * x n for x ∈ c₀
      sorry
    right_inv := by
      -- TODO: Show toCoeffsL1 (ofCoeffs a) = a
      -- Direct from definitions
      sorry
    map_add' := toCoeffsL1.toLinearMap.map_add'
    map_smul' := toCoeffsL1.toLinearMap.map_smul'
  }
  norm_map' := by
    -- TODO: Use toCoeffs_norm_eq
    sorry

end C0DualIsoL1

/-
================================================================================
PART B: (ℓ¹ →L[ℝ] ℝ) ≃ₗᵢ ℓ^∞
================================================================================
-/

section L1DualIsoLinf

/-- Extract bounded sequence from functional on ℓ¹ -/
def toBounded (φ : ℓ¹ →L[ℝ] ℝ) : ℕ → ℝ :=
  fun n => φ (l1.single n 1)  -- φ evaluated on n-th basis vector

/-- toBounded gives a bounded sequence with sup norm = operator norm -/
lemma toBounded_sup_eq (φ : ℓ¹ →L[ℝ] ℝ) :
    ⨆ n, ‖toBounded φ n‖ = ‖φ‖ := by
  -- TODO:
  -- 1. ≤: Each |φ(eₙ)| ≤ ‖φ‖
  -- 2. ≥: Test φ on sign-truncated vectors in ℓ¹
  sorry

/-- toBounded lands in ℓ^∞ -/
def toBoundedLinf : (ℓ¹ →L[ℝ] ℝ) →ₗᵢ[ℝ] ℓ^∞ where
  toLinearMap := {
    toFun := fun φ => ⟨toBounded φ, by
      -- TODO: Show boundedness using toBounded_sup_eq
      sorry⟩
    map_add' := by sorry
    map_smul' := by sorry
  }
  norm_map' := by
    -- TODO: Use toBounded_sup_eq
    sorry

/-- Reconstruct functional from bounded sequence -/
def ofBounded (b : ℓ^∞) : ℓ¹ →L[ℝ] ℝ where
  toLinearMap := {
    toFun := fun x => ∑' n, x.val n * b.val n
    map_add' := by sorry
    map_smul' := by sorry
  }
  cont := by
    -- TODO: Show ‖ofBounded b x‖ ≤ ‖b‖∞ ‖x‖₁
    sorry

/-- ofBounded has norm equal to sup norm -/
lemma ofBounded_norm_eq (b : ℓ^∞) :
    ‖ofBounded b‖ = ‖b‖ := by
  -- TODO: Similar to ofCoeffs_norm_eq
  sorry

/-- The main isometry: ℓ¹ dual ≃ ℓ^∞ -/
def dual_l1_iso_linf : (ℓ¹ →L[ℝ] ℝ) ≃ₗᵢ[ℝ] ℓ^∞ where
  toLinearEquiv := {
    toFun := toBoundedLinf.toLinearMap.toFun
    invFun := ofBounded
    left_inv := by sorry
    right_inv := by sorry
    map_add' := toBoundedLinf.toLinearMap.map_add'
    map_smul' := toBoundedLinf.toLinearMap.map_smul'
  }
  norm_map' := by sorry

end L1DualIsoLinf

/-
================================================================================
PART C: Discharging the axioms
================================================================================
-/

section DischargeAxioms

/-- WLPO implies DualIsBanach for c₀ -/
theorem dual_is_banach_c0_from_WLPO_proof (h : WLPO) : DualIsBanach c₀ := by
  -- TODO:
  -- 1. Use dual_c0_iso_l1 to transport to ℓ¹
  -- 2. Show DualIsBanach ℓ¹ using WLPO
  -- 3. Transport back
  -- Note: Need to understand exact content of DualIsBanach
  sorry

/-- WLPO implies DualIsBanach for c₀ dual -/
theorem dual_is_banach_c0_dual_from_WLPO_proof (h : WLPO) : 
    DualIsBanach (c₀ →L[ℝ] ℝ) := by
  -- TODO:
  -- 1. Use dual_c0_iso_l1 to identify (c₀ →L ℝ) with ℓ¹
  -- 2. Use dual_l1_iso_linf to identify (ℓ¹ →L ℝ) with ℓ^∞
  -- 3. Show DualIsBanach ℓ^∞ using WLPO
  -- 4. Transport back through isometries
  sorry

end DischargeAxioms

end Papers.P2.HB