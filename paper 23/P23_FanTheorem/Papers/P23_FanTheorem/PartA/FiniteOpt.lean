/-
  Paper 23: The Fan Theorem and the Constructive Cost of Optimization
  PartA/FiniteOpt.lean — Finite grid optimization is BISH

  For any finite set of coupling values, the minimum of the free energy
  is computable by finite search. No Fan Theorem needed.
-/
import Papers.P23_FanTheorem.Defs.IsingFreeEnergy
import Mathlib.Data.Finset.Max

namespace Papers.P23

noncomputable section

/-- Finite-grid optimization is BISH.
    For any nonempty finite set of coupling values, there exists
    a minimizer of the Ising free energy. -/
theorem finite_opt_bish (β : ℝ)
    (grid : Finset ℝ) (hne : grid.Nonempty) :
    ∃ J_star ∈ grid, ∀ J ∈ grid,
      isingFreeEnergy β J_star ≤ isingFreeEnergy β J :=
  Finset.exists_min_image grid (isingFreeEnergy β) hne

/-- Finite-grid maximization is also BISH. -/
theorem finite_opt_max_bish (β : ℝ)
    (grid : Finset ℝ) (hne : grid.Nonempty) :
    ∃ J_star ∈ grid, ∀ J ∈ grid,
      isingFreeEnergy β J ≤ isingFreeEnergy β J_star :=
  Finset.exists_max_image grid (isingFreeEnergy β) hne

end

end Papers.P23
