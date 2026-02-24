/-
  Paper 23: The Fan Theorem and the Constructive Cost of Optimization
  Defs/IsingFreeEnergy.lean — 1D Ising free energy definition

  f(β, J) = -log(2 · cosh(β · J))

  The same free energy from Papers 8 and 20, now viewed as a function
  of the coupling constant J for optimization over compact parameter spaces.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Papers.P23

noncomputable section

/-- The 1D Ising free energy per site as a function of coupling J,
    for fixed inverse temperature β:
    f(β, J) = -log(2 · cosh(β · J)). -/
def isingFreeEnergy (β J : ℝ) : ℝ :=
  -Real.log (2 * Real.cosh (β * J))

/-- 2 · cosh(x) > 0 for all x. -/
theorem two_cosh_pos (x : ℝ) : 0 < 2 * Real.cosh x := by
  apply mul_pos (by norm_num : (0 : ℝ) < 2)
  exact Real.cosh_pos x

/-- 2 · cosh(x) ≠ 0 for all x. -/
theorem two_cosh_ne_zero (x : ℝ) : 2 * Real.cosh x ≠ 0 :=
  ne_of_gt (two_cosh_pos x)

end

end Papers.P23
