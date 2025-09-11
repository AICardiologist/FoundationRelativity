/-
  Papers/P2_BidualGap/Constructive/OpNormCore.lean
  Minimal operator-norm core: honest, classical existence of an LUB for the
  value set on the unit ball (no stubs).
-/
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Group.Completeness
import Mathlib.Order.CompleteLattice.Basic

open Set

namespace OpNorm

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Value set of `‖h x‖` on the unit ball. -/
def valueSet (h : X →L[ℝ] ℝ) : Set ℝ :=
  { r | ∃ x, ‖x‖ ≤ 1 ∧ r = ‖h x‖ }

/-- Nonempty: take `x = 0`. -/
lemma valueSet_nonempty (h : X →L[ℝ] ℝ) : (valueSet h).Nonempty := by
  refine ⟨0, ?_⟩
  exact ⟨0, by simp, by simp⟩

/-- Bounded above by `‖h‖`. -/
lemma valueSet_bddAbove (h : X →L[ℝ] ℝ) : BddAbove (valueSet h) := by
  refine ⟨‖h‖, ?_⟩
  intro r hr
  rcases hr with ⟨x, hx, rfl⟩
  calc
    ‖h x‖ ≤ ‖h‖ * ‖x‖ := h.le_opNorm x
    _     ≤ ‖h‖ * 1   := mul_le_mul_of_nonneg_left hx (norm_nonneg _)
    _     = ‖h‖       := by simp

/-- "HasOpNorm" = the value set has a least upper bound. -/
def HasOpNorm (h : X →L[ℝ] ℝ) : Prop :=
  ∃ N : ℝ, IsLUB (valueSet h) N

/-- Classical: any continuous linear functional has an operator norm as an LUB. -/
lemma hasOpNorm_CLF (h : X →L[ℝ] ℝ) : HasOpNorm h := by
  classical
  use sSup (valueSet h)
  exact isLUB_csSup (valueSet_nonempty h) (valueSet_bddAbove h)

/-- The zero map has an operator norm (trivial corollary). -/
lemma hasOpNorm_zero : HasOpNorm (0 : X →L[ℝ] ℝ) :=
  hasOpNorm_CLF (0 : X →L[ℝ] ℝ)

end OpNorm