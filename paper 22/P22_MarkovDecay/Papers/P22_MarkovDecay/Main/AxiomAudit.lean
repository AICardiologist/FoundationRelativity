/-
  Paper 22: Markov's Principle and the Constructive Cost of Eventual Decay
  Main/AxiomAudit.lean — Comprehensive axiom audit

  Two-tier decomposition:
    BISH tier:  [propext, Classical.choice, Quot.sound]
    MP tier:    [propext, Classical.choice, Quot.sound, mp_real_of_mp]

  Classical.choice is a Mathlib infrastructure artifact (Real.exp, tsum, etc.),
  not mathematical content.
-/
import Papers.P22_MarkovDecay.Main.Stratification

namespace Papers.P22

-- ========================================================================
-- Part A: BISH (no custom axioms)
-- ========================================================================
section PartA_Audit

#print axioms detectionTime_pos
-- Expected: [propext, Classical.choice, Quot.sound]

#print axioms detection_time_works
-- Expected: [propext, Classical.choice, Quot.sound]

#print axioms detection_with_witness
-- Expected: [propext, Classical.choice, Quot.sound]

#print axioms partA_summary
-- Expected: [propext, Classical.choice, Quot.sound]

end PartA_Audit

-- ========================================================================
-- Encoded rate: BISH (no custom axioms)
-- ========================================================================
section EncodedRate_Audit

#print axioms encodedRate_eq_zero_iff
-- Expected: [propext, Classical.choice, Quot.sound]

#print axioms encodedRate_nonneg
-- Expected: [propext, Classical.choice, Quot.sound]

#print axioms encodedRate_sub_partialRate_le
-- Expected: [propext, Classical.choice, Quot.sound]

#print axioms witness_from_partial_sum_pos
-- Expected: [propext, Classical.choice, Quot.sound]

end EncodedRate_Audit

-- ========================================================================
-- Part B Forward: MP tier (uses mp_real_of_mp)
-- ========================================================================
section PartB_Forward_Audit

#print axioms eventualDecay_of_mp
-- Expected: [propext, Classical.choice, Quot.sound, mp_real_of_mp]

end PartB_Forward_Audit

-- ========================================================================
-- Part B Backward: BISH tier (NO custom axioms — novel direction)
-- ========================================================================
section PartB_Backward_Audit

#print axioms mp_of_eventualDecay
-- Expected: [propext, Classical.choice, Quot.sound]

end PartB_Backward_Audit

-- ========================================================================
-- Main results
-- ========================================================================
section Main_Audit

#print axioms mp_iff_eventualDecay
-- Expected: [propext, Classical.choice, Quot.sound, mp_real_of_mp]

#print axioms decay_stratification
-- Expected: [propext, Classical.choice, Quot.sound, mp_real_of_mp]

end Main_Audit

-- ========================================================================
-- Hierarchy: BISH (no custom axioms)
-- ========================================================================
section Hierarchy_Audit

#print axioms lpo_implies_mp
-- Expected: [propext]

#print axioms lpo_implies_wlpo
-- Expected: [propext]

#print axioms wlpo_implies_llpo
-- Expected: [propext, Classical.choice, Quot.sound]

end Hierarchy_Audit

end Papers.P22
