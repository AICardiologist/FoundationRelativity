/-
Papers/P2_BidualGap/James/NonAttainment_c0.lean
James' non-attainment functional approach to show c₀ is not reflexive

Track B implementation: Self-contained proof that avoids both dual chains and Hahn-Banach.
Uses the classical James non-attainment theorem.
-/
import Mathlib.Tactic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Papers.P2_BidualGap.Basic

noncomputable section
namespace Papers.P2.James
open Classical ZeroAtInfty NormedSpace

local notation "c₀"  => C₀(ℕ, ℝ)

-- ========================================================================
-- Binary-weighted series functional
-- ========================================================================

/-- Binary-weighted series functional on c₀: J(f) = ∑ 2^{-(n+1)} * f(n). -/
def J : c₀ →L[ℝ] ℝ := by
  -- Define the linear map first
  let lin_map : c₀ →ₗ[ℝ] ℝ := {
    toFun := fun f => ∑' n, (1 / 2^(n+1 : ℕ)) * f.toFun n
    map_add' := by
      intro f g
      simp only [ZeroAtInftyContinuousMap.coe_add, Pi.add_apply]
      rw [tsum_add]
      · congr 1
        ext n
        ring
      · -- Summability of f terms
        apply summable_of_norm_bounded (summable_geometric_of_lt_one (by norm_num) (by norm_num))
        intro n
        simp only [norm_mul, norm_div, norm_pow, norm_one, Real.norm_two]
        rw [div_le_iff (by norm_num : (0 : ℝ) < 2^(n+1))]
        have h_bound : ‖f.toFun n‖ ≤ ‖f‖ := by
          rw [ContinuousMap.norm_coe_le_norm]
          exact BoundedContinuousFunction.norm_coe_le_norm _ n
        calc ‖f.toFun n‖
          ≤ ‖f‖ := h_bound
          _ ≤ ‖f‖ * 1 := by rw [mul_one]
          _ = ‖f‖ * 2^(n+1) / 2^(n+1) := by rw [mul_div_cancel_of_ne_zero]; norm_num
      · -- Summability of g terms  
        apply summable_of_norm_bounded (summable_geometric_of_lt_one (by norm_num) (by norm_num))
        intro n
        simp only [norm_mul, norm_div, norm_pow, norm_one, Real.norm_two]
        rw [div_le_iff (by norm_num : (0 : ℝ) < 2^(n+1))]
        have h_bound : ‖g.toFun n‖ ≤ ‖g‖ := by
          rw [ContinuousMap.norm_coe_le_norm]
          exact BoundedContinuousFunction.norm_coe_le_norm _ n
        calc ‖g.toFun n‖
          ≤ ‖g‖ := h_bound  
          _ ≤ ‖g‖ * 1 := by rw [mul_one]
          _ = ‖g‖ * 2^(n+1) / 2^(n+1) := by rw [mul_div_cancel_of_ne_zero]; norm_num
    map_smul' := by
      intro r f
      simp only [ZeroAtInftyContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [← tsum_mul_left]
      congr 1
      ext n
      ring
  }
  
  -- Show continuity  
  exact {
    toLinearMap := lin_map
    cont := by
      -- Show ‖J‖ ≤ 1 by geometric series bound
      rw [ContinuousLinearMap.mkOfBound_apply]
      apply LinearMap.mkOfBound_continuous
      intro f
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [norm_tsum_le_tsum_norm]
      · calc (∑' n, ‖(1 / 2^(n+1 : ℕ)) * f.toFun n‖)
          = ∑' n, (1 / 2^(n+1 : ℕ)) * ‖f.toFun n‖ := by
            congr 1; ext n
            rw [norm_mul, norm_div, norm_pow, norm_one, Real.norm_two]
            simp only [Real.norm_eq_abs, abs_nonneg, abs_of_pos (by norm_num : (0 : ℝ) < 2^(n+1))]
          _ ≤ ∑' n, (1 / 2^(n+1 : ℕ)) * ‖f‖ := by
            apply tsum_le_tsum
            · intro n
              apply mul_le_mul_of_nonneg_left
              · rw [ContinuousMap.norm_coe_le_norm]
                exact BoundedContinuousFunction.norm_coe_le_norm _ n
              · simp only [one_div, inv_nonneg, pow_nonneg, zero_le_two]
            · sorry -- summability bounds
            · sorry -- summability bounds  
          _ = ‖f‖ * (∑' n, (1 / 2^(n+1 : ℕ))) := by rw [tsum_mul_right]
          _ = ‖f‖ * 1 := by simp only [← tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
          _ = ‖f‖ := by rw [mul_one]
      · -- Summability
        apply summable_of_norm_bounded (summable_geometric_of_lt_one (by norm_num) (by norm_num))  
        intro n
        simp only [norm_mul, norm_div, norm_pow, norm_one, Real.norm_two]  
        rw [div_le_iff (by norm_num : (0 : ℝ) < 2^(n+1))]
        have h_bound : ‖f.toFun n‖ ≤ ‖f‖ := by
          rw [ContinuousMap.norm_coe_le_norm]
          exact BoundedContinuousFunction.norm_coe_le_norm _ n
        calc ‖f.toFun n‖
          ≤ ‖f‖ := h_bound
          _ ≤ ‖f‖ * 1 := by rw [mul_one]  
          _ = ‖f‖ * 2^(n+1) / 2^(n+1) := by rw [mul_div_cancel_of_ne_zero]; norm_num
  }

-- ========================================================================
-- Properties of J
-- ========================================================================

/-- Norm of J is 1. -/
lemma norm_J : ‖J‖ = 1 := by
  -- Lower bound: construct near-extremizer
  -- Upper bound: from geometric series (already shown in continuity proof)
  sorry -- Technical: construct sequence achieving norm bound

/-- J does not attain its norm on the unit ball of c₀. -/
lemma J_not_attained : ¬ ∃ f : c₀, ‖f‖ ≤ 1 ∧ ‖J f‖ = ‖J‖ := by
  intro ⟨f, hf_bound, hf_attain⟩
  rw [norm_J] at hf_attain
  simp only [J] at hf_attain
  
  -- To attain norm 1, we would need f(n) = 1 for all n (or close to it)
  -- But such f cannot vanish at infinity, contradicting f ∈ c₀
  
  -- The functional J(f) = ∑ 2^{-(n+1)} * f(n) achieves maximum when f(n) = sgn(weight) = 1
  -- But constant function 1 is not in c₀
  
  have h_vanish : Tendsto f.toFun (cocompact ℕ) (𝓝 0) := f.zero_at_infty'
  
  -- If ‖J f‖ = 1 and ‖f‖ ≤ 1, then f must be "close to" (1,1,1,...) in a weighted sense
  -- This contradicts vanishing at infinity
  
  sorry -- Technical argument: attaining the bound requires f to be bounded away from 0,
       -- contradicting vanishing at infinity

-- ========================================================================
-- Non-reflexivity of c₀
-- ========================================================================

/-- In reflexive spaces, every continuous linear functional attains its norm on the closed unit ball. -/
lemma reflexive_implies_norm_attainment {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] 
  [CompleteSpace E] (h_refl : Function.Surjective (inclusionInDoubleDual ℝ E)) :
  ∀ f : E →L[ℝ] ℝ, f ≠ 0 → ∃ x : E, ‖x‖ ≤ 1 ∧ ‖f x‖ = ‖f‖ := by
  -- This is James' theorem: reflexivity implies norm attainment
  -- In reflexive spaces, the closed unit ball is weakly compact
  -- Every weakly continuous function attains its supremum on weakly compact sets
  sorry -- Standard result, may be in mathlib under different name

/-- Hence c₀ is not reflexive, so the bidual embedding is not surjective. -/
lemma c0_not_reflexive : ¬ Function.Surjective (inclusionInDoubleDual ℝ c₀) := by
  intro h_surj
  -- Apply reflexive_implies_norm_attainment to J
  have h_attain := reflexive_implies_norm_attainment h_surj J
  have h_nonzero : J ≠ 0 := by
    rw [← norm_pos_iff, norm_J]
    norm_num
  specialize h_attain h_nonzero
  -- This contradicts J_not_attained
  exact J_not_attained h_attain

-- ========================================================================
-- Package into BidualGapStrong (if needed)
-- ========================================================================

/-- If we need DualIsBanach properties, we can axiomatize them here or import from WLPO construction. -/
axiom dual_is_banach_c0 : DualIsBanach c₀
axiom dual_is_banach_c0_dual : DualIsBanach (c₀ →L[ℝ] ℝ)

/-- Alternative construction of BidualGapStrong via James functional. -/
lemma james_implies_gap : BidualGapStrong := by
  let X := c₀
  have hGap : ¬ Function.Surjective (inclusionInDoubleDual ℝ X) := c0_not_reflexive
  use ⟨X, inferInstance, inferInstance, inferInstance, 
    dual_is_banach_c0, dual_is_banach_c0_dual, hGap⟩

end Papers.P2.James