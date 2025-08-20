/-
  OpNormCore: a minimal, Prop-level interface sufficient for Ishihara.lean.

  Intent:
  - Avoids heavy operator-norm / csSup API.
  - Provides just enough structure used by Ishihara:
      * UnitBall
      * valueSet (image of UnitBall under x ↦ |T x|)
      * HasOpNorm (sup/approx spec, Prop-level)
      * zero-functional facts

  This file is mathlib-friendly but very light-touch.
-/
import Mathlib.Analysis.NormedSpace.OperatorNorm

namespace Papers.P2_BidualGap.Constructive
namespace OpNorm

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Unit ball: `{ x | ‖x‖ ≤ 1 }`. -/
def UnitBall (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] : Set X :=
  { x | ‖x‖ ≤ 1 }

/-- `valueSet T` collects the absolute values `|T x|` over the unit ball. -/
def valueSet (T : X →L[ℝ] ℝ) : Set ℝ :=
  { y | ∃ x, x ∈ UnitBall X ∧ y = |T x| }

/-- A Prop-level operator-norm specification with an approximation clause. -/
def HasOpNorm (T : X →L[ℝ] ℝ) : Prop :=
  ∃ op : ℝ,
    0 ≤ op ∧
    (∀ x, x ∈ UnitBall X → |T x| ≤ op) ∧
    (∀ ε > 0, ∃ x, x ∈ UnitBall X ∧ op - ε ≤ |T x|)

/-- `0` lies in the unit ball. -/
@[simp] lemma zero_mem_UnitBall : (0 : X) ∈ UnitBall X := by
  have h : (0 : ℝ) ≤ 1 := le_of_lt (show (0 : ℝ) < 1 from zero_lt_one)
  simpa [UnitBall, norm_zero] using h

/-- Trivial `HasOpNorm` witness for the zero functional. -/
lemma hasOpNorm_zero : HasOpNorm (X:=X) (0 : X →L[ℝ] ℝ) := by
  refine ⟨0, le_rfl, ?upper, ?approx⟩
  · intro x hx; simpa using (by simpa using (le_of_eq (by simpa : |((0 : X →L[ℝ] ℝ) x)| = (0 : ℝ))))
  · intro ε hε
    refine ⟨0, zero_mem_UnitBall (X:=X), ?goal⟩
    -- need: 0 - ε ≤ |(0 : _ →L[ℝ] ℝ) 0| = 0
    -- i.e., -ε ≤ 0, which follows from ε > 0
    simpa [sub_eq_add_neg, abs_zero] using (neg_nonpos.mpr (le_of_lt hε))

/-- `0 ∈ valueSet (0 : X →L[ℝ] ℝ)` via `x = 0`. -/
lemma zero_mem_valueSet_zero : (0 : ℝ) ∈ valueSet (X:=X) (0 : X →L[ℝ] ℝ) := by
  refine ⟨0, zero_mem_UnitBall (X:=X), ?_⟩
  simp

end OpNorm
end Papers.P2_BidualGap.Constructive