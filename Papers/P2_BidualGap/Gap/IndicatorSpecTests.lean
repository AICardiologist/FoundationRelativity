/-
Pin‑safe smoke tests for the §3.1 spec.
-/
import Papers.P2_BidualGap.Gap.IndicatorSpec

open Papers.P2.Gap.BooleanSubLattice

section
variable (A B : Set ℕ)

example : indicatorEqModC0Spec A B ↔ finiteSymmDiff A B :=
  indicatorEqModC0_spec_iff (A := A) (B := B)

-- sanity: symmetric difference is symmetric (by defs)
example : Papers.P2.Gap.BooleanSubLattice.symmDiff A B = Papers.P2.Gap.BooleanSubLattice.symmDiff B A := by
  -- (A \ B) ∪ (B \ A) = (B \ A) ∪ (A \ B)
  -- commutativity of union
  simp only [Papers.P2.Gap.BooleanSubLattice.symmDiff]
  rw [Set.union_comm]

end