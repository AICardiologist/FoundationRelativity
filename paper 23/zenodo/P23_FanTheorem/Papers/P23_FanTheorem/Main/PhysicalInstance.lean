/-
  Paper 23: The Fan Theorem and the Constructive Cost of Optimization
  Main/PhysicalInstance.lean — Ising free energy optimization from FT

  The Fan Theorem implies that the Ising free energy attains its
  minimum on any compact coupling interval [a, b].
-/
import Papers.P23_FanTheorem.PartA.Continuity
import Papers.P23_FanTheorem.PartB.PartB_Main

namespace Papers.P23

noncomputable section

/-- The Fan Theorem implies the Ising free energy attains its minimum
    on the compact coupling interval [a, b]. -/
theorem ising_opt_of_ft (hft : FanTheorem)
    (β : ℝ) (a b : ℝ) (hab : a < b) :
    ∃ J_star ∈ Set.Icc a b,
      ∀ J ∈ Set.Icc a b,
        isingFreeEnergy β J_star ≤ isingFreeEnergy β J := by
  exact ft_iff_compact_opt.mp hft a b hab (isingFreeEnergy β)
    (isingFreeEnergy_continuousOn β a b)

-- Axiom audit
-- Expected: [propext, Classical.choice, Quot.sound]
#print axioms ising_opt_of_ft

end

end Papers.P23
