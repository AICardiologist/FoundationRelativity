/-
  Paper 23: The Fan Theorem and the Constructive Cost of Optimization
  PartA/PartA_Main.lean — Part A summary and axiom audit

  Part A (BISH): With specific functions or finite grids,
  optimization is fully constructive. No Fan Theorem required.
-/
import Papers.P23_FanTheorem.PartA.Continuity
import Papers.P23_FanTheorem.PartA.FiniteOpt

namespace Papers.P23

/-- Part A summary: finite optimization and continuity are BISH. -/
theorem partA_summary :
    -- The Ising free energy is continuous
    (∀ β : ℝ, Continuous (isingFreeEnergy β)) ∧
    -- Finite grid optimization works
    (∀ β : ℝ, ∀ grid : Finset ℝ, grid.Nonempty →
      ∃ J_star ∈ grid, ∀ J ∈ grid,
        isingFreeEnergy β J_star ≤ isingFreeEnergy β J) :=
  ⟨isingFreeEnergy_continuous,
   fun β grid hne => finite_opt_bish β grid hne⟩

-- Axiom audit: Part A is BISH (no custom axioms)
-- Expected: [propext, Classical.choice, Quot.sound]
#print axioms isingFreeEnergy_continuous
#print axioms finite_opt_bish
#print axioms partA_summary

end Papers.P23
