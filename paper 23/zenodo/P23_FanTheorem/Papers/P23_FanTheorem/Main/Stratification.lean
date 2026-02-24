/-
  Paper 23: The Fan Theorem and the Constructive Cost of Optimization
  Main/Stratification.lean — Three-branch partial order

  The calibration table is now a genuine partial order with three
  independent branches:

        LPO
       / | \
      /  |  \
   WLPO  MP  ...
    |
   LLPO
    |
   BISH            FT (independent of all above)

  FT is independent of LPO, WLPO, LLPO, and MP (Berger 2005).
-/
import Papers.P23_FanTheorem.PartA.PartA_Main
import Papers.P23_FanTheorem.PartB.PartB_Main
import Papers.P23_FanTheorem.Defs.Principles

namespace Papers.P23

/-- The three-branch stratification:
    - Omniscience chain: LPO → WLPO → LLPO
    - Markov branch: LPO → MP
    - Compactness branch: FT ↔ CompactOptimization (independent of all above) -/
theorem fan_stratification :
    -- Omniscience chain
    (LPO → WLPO) ∧
    (WLPO → LLPO) ∧
    -- Markov branch
    (LPO → MarkovPrinciple) ∧
    -- Compactness branch
    (FanTheorem ↔ CompactOptimization) :=
  ⟨lpo_implies_wlpo, wlpo_implies_llpo, lpo_implies_mp, ft_iff_compact_opt⟩

-- FT is independent of LPO, WLPO, LLPO, MP:
-- • Brouwerian models satisfy FT but not LPO (so FT ⊬ LPO)
-- • Russian recursive models satisfy LPO but not FT (so LPO ⊬ FT)
-- • Independence from MP follows similarly
-- These are standard model-theoretic results (Berger 2005, Bridges-Vîță 2006)

-- Axiom audit
-- Expected: [propext, Classical.choice, Quot.sound]
#print axioms fan_stratification

end Papers.P23
