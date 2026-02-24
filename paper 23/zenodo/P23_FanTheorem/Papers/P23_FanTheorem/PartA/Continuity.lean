/-
  Paper 23: The Fan Theorem and the Constructive Cost of Optimization
  PartA/Continuity.lean — Ising free energy is continuous

  f(β, J) = -log(2 · cosh(β · J)) is continuous in J.
  This is BISH: composition of explicitly continuous functions.
-/
import Papers.P23_FanTheorem.Defs.IsingFreeEnergy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace Papers.P23

noncomputable section

/-- The Ising free energy is continuous in J (for any β). -/
theorem isingFreeEnergy_continuous (β : ℝ) :
    Continuous (isingFreeEnergy β) := by
  unfold isingFreeEnergy
  apply Continuous.neg
  apply Continuous.log
  · exact continuous_const.mul (Real.continuous_cosh.comp (continuous_const.mul continuous_id))
  · intro J
    exact two_cosh_ne_zero (β * J)

/-- ContinuousOn version for [a, b]. -/
theorem isingFreeEnergy_continuousOn (β : ℝ) (a b : ℝ) :
    ContinuousOn (isingFreeEnergy β) (Set.Icc a b) :=
  (isingFreeEnergy_continuous β).continuousOn

end

end Papers.P23
