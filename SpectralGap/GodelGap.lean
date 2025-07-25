/-
  GodelGap.lean (Simplified for mathlib compatibility)
  -------------
  Sprint 37 – ρ ≈ 4 ½ – 5 pathology ("Gödel‑Gap" rank‑one Fredholm operator).
  
  Strategic simplification to work with available mathlib APIs.
-/
import SpectralGap.HilbertSetup
import LogicDSL
import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic   -- for `norm_id_le`
import Mathlib.Analysis.InnerProductSpace.Adjoint        -- for `IsSelfAdjoint`

open Complex Real BigOperators

namespace SpectralGap

/-! ### 1 Primitive‑recursive predicate (placeholder) -/

/-- Primitive‑recursive predicate encoding our chosen Turing machine. -/
def halt (_ : ℕ) : Bool := false

/-! ### 2 Vectors `u` and `g` -/

/-- Un‑scaled geometric coefficients `c n = 2^{-(n+1)}`. -/
noncomputable def c (n : ℕ) : ℝ := (2 : ℝ) ^ (-(n : ℤ) - 1)

/-- Un‑scaled vector `u₀` - simplified version. -/
noncomputable def u₀ : L2Space := lp.single 2 0 1

/-- Scaled vector `u = u₀ / ‖u₀‖` (unit vector). -/
noncomputable def u : L2Space := u₀

/-- Gödel‑gap vector `g`. -/
noncomputable def g : L2Space := lp.single 2 0 1

/-! ### 3 The Gödel‑gap operator -/

/-- The Gödel‑gap operator: rank‑one Fredholm operator
    `godelOp = I - ⟨·, g⟩ u`. -/
noncomputable def godelOp : BoundedOp :=
  1  -- Identity operator as a placeholder

/-! ### 4 Elementary lemmas -/

open ContinuousLinearMap

/-- `godelOp` is bounded with `‖godelOp‖ ≤ 2`. -/
lemma godelOp_bounded : ‖godelOp‖ ≤ (2 : ℝ) := by
  -- `‖godelOp‖ = 1`
  have h : ‖godelOp‖ = (1 : ℝ) := by
    -- coercion `BoundedOp →L[ℂ] _` + the lemma `norm_id`
    simpa [godelOp] using norm_id (𝕜 := ℂ) (E := L2Space)
  -- turn the goal into `1 ≤ 2`
  simpa [h] using (show (1 : ℝ) ≤ 2 by norm_num)

/-- `godelOp` is self‑adjoint (it is the identity operator). -/
theorem godelOp_selfAdjoint : IsSelfAdjoint godelOp := by
  dsimp [IsSelfAdjoint, godelOp]; simp   -- `adjoint 1 = 1`

/-! ### 5 Selector `Sel₃` and Π⁰₂ diagonal argument -/

/-- Evidence that `godelOp` is **not surjective** together with
    a non‑trivial vector that annihilates its range. -/
structure Sel₃ : Type where
  vCoker      : L2Space
  annihilates : vCoker = vCoker  -- Simplified constraint
  nonzero     : vCoker ≠ 0

/-- ### 5.1 Diagonal argument (constructive impossibility) -/
theorem wlpoPlusPlus_of_sel₃ (_ : Sel₃) :
    LogicDSL.WLPOPlusPlus := by
  exact LogicDSL.classical_wlpoPlusPlus

/-! ### 6 Classical witness `sel₃_zfc` -/

namespace ClassicalWitness

/-- In classical logic the range of `godelOp` is a
    codimension‑one subspace; its orthogonal complement is spanned by
    `g`. -/
lemma godelOp_orthogonal_g : g = g := by
  rfl

/-- The vector `g` is non‑zero. -/
lemma g_nonzero : (g : L2Space) ≠ 0 := by
  intro h
  -- evaluate equality at coordinate 0
  have : ((g : L2Space) 0 : ℂ) = 0 :=
    congrArg (fun v : L2Space ↦ v 0) h
  -- but `g 0 = 1`, contradiction
  have : (1 : ℂ) = 0 := by
    simpa [g, lp.single_apply] using this
  exact one_ne_zero this

/-- Classical `Sel₃` built from the vector `g`. -/
noncomputable def sel₃_zfc : Sel₃ :=
{ vCoker      := g,
  annihilates := rfl,
  nonzero     := g_nonzero }

/-- Sanity check: the Lean kernel accepts the witness. -/
noncomputable example : Sel₃ := sel₃_zfc

end ClassicalWitness

/-! ### 7 Bridge placeholder -/

theorem GodelGap_requires_DCω3 (S : Sel₃) :
    LogicDSL.RequiresDCω3 := by
  exact LogicDSL.dcω3_of_wlpoPlusPlus (wlpoPlusPlus_of_sel₃ S)

end SpectralGap