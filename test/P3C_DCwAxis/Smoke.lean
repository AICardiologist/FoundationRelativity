import Papers.P3C_DCwAxis.DCw_Baire
-- import Mathlib.Topology.Basic -- Would be needed for IsOpen/Dense

open Papers.P3C.DCw

/-!
# Smoke test for P3C

When topology is available, this will test:
Uₙ := { x | x n ≠ 0 } is open and dense, so the intersection is nonempty

For now, just verify the theorem statement compiles.
-/

-- example (hDC : DCω) :
--   ∃ x : Seq, ∀ n, x n ≠ 0 := by
--   have hB := baireNN_of_DCω hDC
--   let U : Nat → Set Seq := fun n => {x | x n ≠ 0}
--   have hOpen : ∀ n, IsOpen (U n) := by
--     intro n; -- continuity of the n-th coordinate + openness of {m ≠ 0}
--     sorry
--   have hDense : ∀ n, Dense (U n) := by
--     intro n; -- easy: tweak one position in any cylinder
--     sorry
--   rcases hB U hOpen hDense with ⟨x, hx⟩; exact ⟨x, hx⟩