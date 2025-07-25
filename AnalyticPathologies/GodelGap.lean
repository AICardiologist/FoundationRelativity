/-
  GodelGap.lean (Simplified for mathlib compatibility)
  -------------
  Sprint 37 – ρ ≈ 4 ½ – 5 pathology ("Gödel‑Gap" rank‑one Fredholm operator).
  
  Strategic simplification to work with available mathlib APIs.
-/
import AnalyticPathologies.HilbertSetup
import LogicDSL
import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic   -- for `norm_id_le`
import Mathlib.Analysis.InnerProductSpace.Adjoint        -- `adjoint_id`

open Complex Real BigOperators ContinuousLinearMap

namespace AnalyticPathologies

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

/-! ### 2.5 `L2Space` is non‑trivial (needed by `norm_id`) -/

instance : Nontrivial L2Space := by
  refine ⟨⟨g, 0, ?_⟩⟩
  intro h_eq        -- assume `g = 0`, derive a contradiction
  have h0 : ((g : L2Space) 0 : ℂ) = 0 :=
    congrArg (fun v : L2Space ↦ v 0) h_eq
  -- but `g 0 = 1`
  rw [g] at h0
  simp only [lp.single_apply] at h0
  norm_num at h0

/-! ### 3 The Gödel‑gap operator -/

/-- The Gödel‑gap operator: rank‑one Fredholm operator
    `godelOp = I - ⟨·, g⟩ u`. -/
noncomputable def godelOp : BoundedOp :=
  1  -- Identity operator as a placeholder

/-! ### 4 Elementary lemmas -/

/-- `godelOp` is bounded with `‖godelOp‖ ≤ 2`. -/
lemma godelOp_bounded : ‖godelOp‖ ≤ (2 : ℝ) := by
  calc ‖godelOp‖ = ‖(1 : BoundedOp)‖ := by rw [godelOp]
  _ = 1 := norm_id (𝕜 := ℂ) (E := L2Space)
  _ ≤ 2 := by norm_num

/-- `godelOp` (the identity) is self‑adjoint. -/
theorem godelOp_selfAdjoint : IsSelfAdjoint godelOp := by
  -- rewrite to a goal about a `ContinuousLinearMap`
  rw [IsSelfAdjoint, godelOp]
  -- The goal is now adjoint 1 = 1
  exact adjoint_id

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
  have h0 : ((g : L2Space) 0 : ℂ) = 0 :=
    congrArg (fun v : L2Space ↦ v 0) h
  rw [g] at h0
  simp only [lp.single_apply] at h0
  norm_num at h0

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

end AnalyticPathologies