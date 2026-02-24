/-
  Paper 20: WLPO Equivalence via Ising Magnetization Phase Classification
  Defs/Magnetization.lean — Infinite-volume magnetization (closed form)

  The 1D Ising model infinite-volume magnetization is:
    m(∞, β, J, h) = sinh(β·h) / √(sinh²(β·h) + exp(-4·β·J))

  Key property: m(∞, β, J, h) = 0  ⟺  h = 0
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace Papers.P20

noncomputable section

/-- The discriminant term: sinh²(β·h) + exp(-4·β·J).
    Always positive for β > 0, J > 0. -/
def magDiscriminant (β J h : ℝ) : ℝ :=
  (Real.sinh (β * h)) ^ 2 + Real.exp (-(4 * β * J))

/-- The discriminant is strictly positive for β > 0, J > 0. -/
theorem magDiscriminant_pos (_hβ : 0 < β) (_hJ : 0 < J) (h : ℝ) :
    0 < magDiscriminant β J h := by
  unfold magDiscriminant
  have hexp : 0 < Real.exp (-(4 * β * J)) := Real.exp_pos _
  have hsq : 0 ≤ (Real.sinh (β * h)) ^ 2 := sq_nonneg _
  linarith

/-- The infinite-volume magnetization of the 1D Ising model. -/
def magnetization_inf (β J h : ℝ) : ℝ :=
  Real.sinh (β * h) / Real.sqrt (magDiscriminant β J h)

end

end Papers.P20
