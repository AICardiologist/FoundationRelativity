/-
  Paper 22: Markov's Principle and the Constructive Cost of Eventual Decay
  Main/Hierarchy.lean — Hierarchy placement

  MP sits off the main LLPO < WLPO < LPO chain:
  - LPO → MP (trivial)
  - MP is independent of LLPO and WLPO (standard, not formalized)

  The calibration table becomes a partial order:
        LPO
       / | \
      /  |  \
   WLPO  MP  ...
    |
   LLPO
    |
   BISH
-/
import Papers.P22_MarkovDecay.Defs.Markov

namespace Papers.P22

-- LPO → MP is already proved in Defs/Markov.lean as lpo_implies_mp.
-- Re-export here for assembly.

/-- LPO implies Markov's Principle (re-export for Stratification). -/
theorem mp_of_lpo : LPO → MarkovPrinciple := lpo_implies_mp

-- Axiom audit
-- Expected: [propext]
#print axioms mp_of_lpo
#print axioms lpo_implies_wlpo
#print axioms wlpo_implies_llpo

end Papers.P22
