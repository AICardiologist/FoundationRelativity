/-
  Paper 23: The Fan Theorem and the Constructive Cost of Optimization
  PartB/PartB_Main.lean — Main equivalence: FT ↔ CompactOptimization

  Central result: the Fan Theorem (defined as EVT_max) is equivalent
  to compact optimization on arbitrary [a,b].

  Since FanTheorem := EVT_max by definition, this involves NO custom axioms.
-/
import Papers.P23_FanTheorem.PartB.EVTEquiv
import Papers.P23_FanTheorem.PartB.CompactOpt

namespace Papers.P23

-- ========================================================================
-- Main equivalence
-- ========================================================================

/-- Theorem (Main Equivalence):
    The Fan Theorem ↔ CompactOptimization.

    The Fan Theorem is defined as EVT_max (Berger 2005).
    Zero custom axioms in the proof. -/
theorem ft_iff_compact_opt : FanTheorem ↔ CompactOptimization := by
  unfold FanTheorem
  constructor
  · intro hmax
    exact compact_opt_of_evt_min (evt_min_of_evt_max hmax)
  · intro hco
    exact evt_max_of_evt_min (evt_min_of_compact_opt hco)

-- Axiom audit
-- Expected: [propext, Classical.choice, Quot.sound]
-- NO custom axioms!
#print axioms ft_iff_compact_opt

end Papers.P23
