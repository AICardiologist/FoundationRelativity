/-
  Paper 20: WLPO Equivalence via Ising Magnetization Phase Classification
  PartA/SpinFlip.lean — Zero-field magnetization vanishes (Z₂ symmetry)

  For h = 0, the spin-flip symmetry σ → -σ gives m(∞, β, J, 0) = 0.
  In the closed form: sinh(β·0) = sinh(0) = 0, so m = 0/√(...) = 0.
-/
import Papers.P20_WLPOMagnetization.Defs.Magnetization

namespace Papers.P20

/-- The magnetization at zero external field vanishes.
    This is a consequence of the Z₂ spin-flip symmetry of the Ising model.
    In closed form: sinh(β·0) = 0, so m = 0/√(...) = 0. -/
theorem magnetization_inf_zero_field (β J : ℝ) :
    magnetization_inf β J 0 = 0 := by
  unfold magnetization_inf
  simp [mul_zero, Real.sinh_zero]

end Papers.P20
