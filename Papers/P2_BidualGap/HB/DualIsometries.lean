/-
Papers/P2_BidualGap/HB/DualIsometries.lean

Isometric identifications to discharge the two DualIsBanach axioms:
1. (c₀ →L[ℝ] ℝ) ≃ₗᵢ lp (fun _ : ℕ => ℝ) 1
2. (lp (fun _ : ℕ => ℝ) 1 →L[ℝ] ℝ) ≃ₗᵢ lp (fun _ : ℕ => ℝ) ⊤

These will allow us to prove:
- WLPO → DualIsBanach c₀
- WLPO → DualIsBanach (c₀ →L[ℝ] ℝ)
-/

import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Papers.P2_BidualGap.Basic
import Papers.P2_BidualGap.HB.DirectDual

namespace Papers.P2.HB

open scoped BigOperators

/-
================================================================================
PART A: (c₀ →L[ℝ] ℝ) ≃ₗᵢ lp (fun _ : ℕ => ℝ) 1
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

/-- The coefficients are summable with lp (fun _ : ℕ => ℝ) 1 norm equal to operator norm -/
lemma toCoeffs_summable (f : c₀ →L[ℝ] ℝ) : 
    Summable (fun n => ‖f (e n)‖) := by
  -- TODO: Use the fact that for any finite F ⊆ ℕ,
  -- ∑_{n ∈ F} |f(e n)| ≤ ‖f‖ (via signVector test)
  -- This is already proven in DirectDual.lean
  sorry

/-- The coefficients satisfy lp (fun _ : ℕ => ℝ) 1 norm equals operator norm -/
lemma toCoeffs_norm_eq (f : c₀ →L[ℝ] ℝ) :
    ∑' n, ‖f (e n)‖ = ‖f‖ := by
  -- TODO: 
  -- 1. Show ≤ using finite sum bounds
  -- 2. Show ≥ by testing f on truncated sign vectors
  -- (Reuse signVector lemmas from DirectDual.lean)
  sorry

/-- toCoeffs lands in lp (fun _ : ℕ => ℝ) 1 -/
def toCoeffsL1 : (c₀ →L[ℝ] ℝ) →ₗᵢ[ℝ] (lp (fun _ : ℕ => ℝ) 1) where
  toLinearMap := {
    toFun := fun f => ⟨toCoeffs f, by
      -- TODO: Show membership in lp (fun _ : ℕ => ℝ) 1
      -- Use toCoeffs_summable
      sorry⟩
    map_add' := by sorry
    map_smul' := by sorry
  }
  norm_map' := by
    -- TODO: Use toCoeffs_norm_eq
    sorry

/-- Reconstruct a functional from lp (fun _ : ℕ => ℝ) 1 coefficients -/
def ofCoeffs (a : lp (fun _ : ℕ => ℝ) 1) : c₀ →L[ℝ] ℝ where
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

/-- ofCoeffs has norm equal to lp (fun _ : ℕ => ℝ) 1 norm -/
lemma ofCoeffs_norm_eq (a : lp (fun _ : ℕ => ℝ) 1) :
    ‖ofCoeffs a‖ = ‖a‖ := by
  -- TODO:
  -- 1. ≤ direction: standard estimate
  -- 2. ≥ direction: test on sign vectors for a
  sorry

/-- The main isometry: c₀ dual ≃ lp (fun _ : ℕ => ℝ) 1 -/
def dual_c0_iso_l1 : (c₀ →L[ℝ] ℝ) ≃ₗᵢ[ℝ] lp (fun _ : ℕ => ℝ) 1 where
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
PART B: (lp (fun _ : ℕ => ℝ) 1 →L[ℝ] ℝ) ≃ₗᵢ lp (fun _ : ℕ => ℝ) ⊤
================================================================================
-/

section L1DualIsoLinf

/-- Extract bounded sequence from functional on lp (fun _ : ℕ => ℝ) 1 -/
def toBounded (φ : lp (fun _ : ℕ => ℝ) 1 →L[ℝ] ℝ) : ℕ → ℝ :=
  fun n => φ (lp.single 1 (fun _ => (1 : ℝ)) n 1)  -- φ evaluated on n-th basis vector

/-- toBounded gives a bounded sequence with sup norm = operator norm -/
lemma toBounded_sup_eq (φ : lp (fun _ : ℕ => ℝ) 1 →L[ℝ] ℝ) :
    ⨆ n, ‖toBounded φ n‖ = ‖φ‖ := by
  -- TODO:
  -- 1. ≤: Each |φ(eₙ)| ≤ ‖φ‖
  -- 2. ≥: Test φ on sign-truncated vectors in lp (fun _ : ℕ => ℝ) 1
  sorry

/-- toBounded lands in lp (fun _ : ℕ => ℝ) ⊤ -/
def toBoundedLinf : (lp (fun _ : ℕ => ℝ) 1 →L[ℝ] ℝ) →ₗᵢ[ℝ] lp (fun _ : ℕ => ℝ) ⊤ where
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
def ofBounded (b : lp (fun _ : ℕ => ℝ) ⊤) : lp (fun _ : ℕ => ℝ) 1 →L[ℝ] ℝ where
  toLinearMap := {
    toFun := fun x => ∑' n, x.val n * b.val n
    map_add' := by sorry
    map_smul' := by sorry
  }
  cont := by
    -- TODO: Show ‖ofBounded b x‖ ≤ ‖b‖∞ ‖x‖₁
    sorry

/-- ofBounded has norm equal to sup norm -/
lemma ofBounded_norm_eq (b : lp (fun _ : ℕ => ℝ) ⊤) :
    ‖ofBounded b‖ = ‖b‖ := by
  -- TODO: Similar to ofCoeffs_norm_eq
  sorry

/-- The main isometry: lp (fun _ : ℕ => ℝ) 1 dual ≃ lp (fun _ : ℕ => ℝ) ⊤ -/
def dual_l1_iso_linf : (lp (fun _ : ℕ => ℝ) 1 →L[ℝ] ℝ) ≃ₗᵢ[ℝ] lp (fun _ : ℕ => ℝ) ⊤ where
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
  -- 1. Use dual_c0_iso_l1 to transport to lp (fun _ : ℕ => ℝ) 1
  -- 2. Show DualIsBanach lp (fun _ : ℕ => ℝ) 1 using WLPO
  -- 3. Transport back
  -- Note: Need to understand exact content of DualIsBanach
  sorry

/-- WLPO implies DualIsBanach for c₀ dual -/
theorem dual_is_banach_c0_dual_from_WLPO_proof (h : WLPO) : 
    DualIsBanach (c₀ →L[ℝ] ℝ) := by
  -- TODO:
  -- 1. Use dual_c0_iso_l1 to identify (c₀ →L ℝ) with lp (fun _ : ℕ => ℝ) 1
  -- 2. Use dual_l1_iso_linf to identify (lp (fun _ : ℕ => ℝ) 1 →L ℝ) with lp (fun _ : ℕ => ℝ) ⊤
  -- 3. Show DualIsBanach lp (fun _ : ℕ => ℝ) ⊤ using WLPO
  -- 4. Transport back through isometries
  sorry

end DischargeAxioms

end Papers.P2.HB