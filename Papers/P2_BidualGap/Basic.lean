/-
  Papers/P2_BidualGap/Basic.lean
  Minimal core definitions used by Paper 2.
-/

import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Group.Completeness

namespace Papers.P2

/-- The bidual gap: there exists a real Banach space `X` whose canonical map
    into the bidual is not surjective. -/
def BidualGap : Prop :=
  ∃ (X : Type*) (_ : NormedAddCommGroup X) (_ : NormedSpace ℝ X) (_ : CompleteSpace X),
    ¬ Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X)

/-- WLPO: Weak Limited Principle of Omniscience. -/
def WLPO : Prop :=
  ∀ (α : ℕ → Bool), (∀ n, α n = false) ∨ ¬ (∀ n, α n = false)

end Papers.P2