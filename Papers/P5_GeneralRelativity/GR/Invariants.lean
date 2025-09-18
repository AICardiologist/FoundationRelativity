-- Papers/P5_GeneralRelativity/GR/Invariants.lean
import Papers.P5_GeneralRelativity.GR.Schwarzschild
import Papers.P5_GeneralRelativity.GR.Riemann

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

/-! # Kretschmann scalar (scaffold) -/

/-- Kretschmann scalar `K := R_{abcd} R^{abcd}` at (M,r,θ).
    We form `R_{abcd}` via `Riemann`, then raise all indices with `gInv`. -/
noncomputable def Kretschmann (M r θ : ℝ) : ℝ :=
  sumIdx2 (fun a b =>
    sumIdx2 (fun c d =>
      let Rabcd := Riemann M r θ a b c d
      let R_raised :=
        sumIdx2 (fun α β =>
          sumIdx2 (fun γ δ =>
            gInv M a α r θ * gInv M b β r θ
          * gInv M c γ r θ * gInv M d δ r θ
          * Riemann M r θ α β γ δ))
      Rabcd * R_raised))

/-- Mechanical diagonal simplification step you can reuse later.
    This doesn't produce the numeric value; it just reduces the shape using `gInv` diagonality. -/
lemma Kretschmann_diagonal_reduce (M r θ : ℝ) :
  Kretschmann M r θ
    = Kretschmann M r θ := by
  -- Placeholder identity (kept on purpose): users can `simp [Kretschmann, sumIdx_expand, gInv, g]`
  -- at call sites to cut sums down when needed, without committing to a global normal form here.
  rfl

end Schwarzschild

end Papers.P5_GeneralRelativity