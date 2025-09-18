-- Papers/P5_GeneralRelativity/GR/Invariants.lean
import Papers.P5_GeneralRelativity.GR.Schwarzschild

namespace Papers.P5_GeneralRelativity
open Papers.P5_GeneralRelativity
open Real

namespace Schwarzschild
open Idx

/-- Ricci scalar `R := g^{μν} R_{μν}` at (M,r,θ). Uses your index/sum helpers. -/
noncomputable def RicciScalar (M r θ : ℝ) : ℝ :=
  sumIdx2 (fun μ ν => gInv M μ ν r θ * Ricci M r θ μ ν)

section Exterior

/-- On the exterior (and away from the axis), the Ricci scalar vanishes. -/
theorem RicciScalar_exterior_zero
    (M r θ : ℝ) (hM : 0 < M) (hr : 2*M < r) (hθ : 0 < θ ∧ θ < Real.pi) :
    RicciScalar M r θ = 0 := by
  classical
  -- Use the existing Ricci scalar vanishing theorem that's already proven
  -- This leverages all the existing infrastructure without duplicating work
  exact Ricci_scalar_vanishes M r θ hM hr hθ

end Exterior

/-
TODO: Kretschmann scalar K = R_{abcd} R^{abcd}
Will be added after Riemann tensor is implemented.
For now, focusing on Ricci scalar R = g^{μν} R_{μν} = 0.
-/

end Schwarzschild

end Papers.P5_GeneralRelativity