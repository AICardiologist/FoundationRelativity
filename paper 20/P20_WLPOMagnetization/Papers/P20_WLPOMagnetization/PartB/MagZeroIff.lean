/-
  Paper 20: WLPO Equivalence via Ising Magnetization Phase Classification
  PartB/MagZeroIff.lean — Core equivalence: m(∞, β, J, h) = 0 ↔ h = 0

  The 1D Ising model has no spontaneous magnetization:
    m(∞, β, J, h) = sinh(β·h) / √(sinh²(β·h) + exp(-4·β·J))
  vanishes if and only if h = 0.

  Proof:
    Forward: m = 0 → sinh(β·h)/√(D) = 0 → sinh(β·h) = 0 (denom ≠ 0)
             → β·h = 0 → h = 0 (since β > 0)
    Backward: h = 0 → sinh(0) = 0 → 0/√(D) = 0
-/
import Papers.P20_WLPOMagnetization.PartA.SpinFlip
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

namespace Papers.P20

/-- The √(discriminant) is positive for β > 0, J > 0. -/
theorem sqrt_magDiscriminant_pos (hβ : 0 < β) (hJ : 0 < J) (h : ℝ) :
    0 < Real.sqrt (magDiscriminant β J h) :=
  Real.sqrt_pos_of_pos (magDiscriminant_pos hβ hJ h)

/-- The √(discriminant) is nonzero for β > 0, J > 0. -/
theorem sqrt_magDiscriminant_ne_zero (hβ : 0 < β) (hJ : 0 < J) (h : ℝ) :
    Real.sqrt (magDiscriminant β J h) ≠ 0 :=
  ne_of_gt (sqrt_magDiscriminant_pos hβ hJ h)

/-- Core theorem: The infinite-volume magnetization vanishes
    if and only if the external field is zero. -/
theorem magnetization_inf_eq_zero_iff (hβ : 0 < β) (hJ : 0 < J) (h : ℝ) :
    magnetization_inf β J h = 0 ↔ h = 0 := by
  constructor
  · -- Forward: m = 0 → h = 0
    intro hm
    unfold magnetization_inf at hm
    -- Division by nonzero denominator: numerator must be zero
    have hdenom := sqrt_magDiscriminant_ne_zero hβ hJ h
    rw [div_eq_zero_iff] at hm
    cases hm with
    | inl hsinh =>
      -- sinh(β·h) = 0 → β·h = 0 → h = 0
      rw [Real.sinh_eq_zero] at hsinh
      rcases mul_eq_zero.mp hsinh with hβ0 | hh0
      · exact absurd hβ0 (ne_of_gt hβ)
      · exact hh0
    | inr habsurd => exact absurd habsurd hdenom
  · -- Backward: h = 0 → m = 0
    intro heq
    subst heq
    exact magnetization_inf_zero_field β J

end Papers.P20
