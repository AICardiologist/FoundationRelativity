/-
  Papers/P2_BidualGap/Constructive/OpNormCore.lean
  
  Minimal OpNorm core (no sorries) used by Ishihara.lean
  Provides just the definitions needed without the deprecated proofs.
-/
import Mathlib.Analysis.NormedSpace.OperatorNorm
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.CompleteLattice

open scoped BigOperators
open Set

namespace OpNorm

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Closed unit ball of `X` (by norm). -/
def UnitBall (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] : Set X :=
  {x | ‖x‖ ≤ 1}

/-- The value set of a continuous linear functional `T : X →L[ℝ] ℝ` over the unit ball. -/
def valueSet (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
  (T : X →L[ℝ] ℝ) : Set ℝ :=
  {t | ∃ x ∈ UnitBall X, ‖T x‖ = t}

/-- Existence of a least upper bound for the value set: sufficient for the uses in Ishihara. -/
structure HasOpNorm (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
  (T : X →L[ℝ] ℝ) : Prop :=
  (exists_lub : ∃ r : ℝ, IsLUB (valueSet X T) r)

/-- The value set is nonempty (contains at least 0). -/
lemma valueSet_nonempty (T : X →L[ℝ] ℝ) : (valueSet X T).Nonempty := by
  refine ⟨0, ?_⟩
  refine ⟨0, ?_, ?_⟩
  · simp [UnitBall]
  · simp

/-- For the zero functional, the value set is `{0}`. -/
lemma valueSet_zero :
  valueSet X (0 : X →L[ℝ] ℝ) = ({0} : Set ℝ) := by
  ext t; constructor
  · intro ⟨x, _, hx⟩
    simp at hx
    exact hx
  · intro ht
    simp at ht
    rw [ht]
    refine ⟨(0 : X), ?_, ?_⟩
    · simp [UnitBall]
    · simp

/-- The zero functional trivially admits an operator-norm bound. -/
lemma hasOpNorm_zero : HasOpNorm (X:=X) (0 : X →L[ℝ] ℝ) := by
  refine ⟨0, ?_⟩
  rw [valueSet_zero]
  constructor
  · intro _ hx
    simp at hx
    exact le_of_eq hx.symm
  · intro _ h
    exact h 0 (by simp)

end OpNorm