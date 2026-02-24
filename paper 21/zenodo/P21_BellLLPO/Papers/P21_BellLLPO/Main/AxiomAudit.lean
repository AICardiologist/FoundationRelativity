/-
  Paper 21: Bell Nonlocality and the Constructive Cost of Disjunction: LLPO
  Main/AxiomAudit.lean — Comprehensive axiom audit

  Three-tier decomposition verified by #print axioms:
    Part A (BISH): propext, Classical.choice, Quot.sound only
    Part B (LLPO): adds llpo_real_of_llpo
    Hierarchy:      propext, Classical.choice, Quot.sound only
-/
import Papers.P21_BellLLPO.Main.Stratification

namespace Papers.P21

-- ============================================================
-- PART A: BISH — No custom axioms
-- Expected: [propext, Classical.choice, Quot.sound]
-- ============================================================
#print axioms chsh_bound
#print axioms chsh_abs_bound
#print axioms S_quantum_gt_two
#print axioms neg_lhv
#print axioms partA_summary

-- ============================================================
-- PART B: LLPO — One custom axiom
-- ============================================================

-- Forward (LLPO → BellSignDecision):
-- Expected: [propext, Classical.choice, Quot.sound, llpo_real_of_llpo]
#print axioms bell_sign_of_llpo

-- Backward (BellSignDecision → LLPO):
-- Expected: [propext, Classical.choice, Quot.sound] — NO custom axioms
#print axioms llpo_of_bell_sign

-- Main equivalence:
-- Expected: [propext, Classical.choice, Quot.sound, llpo_real_of_llpo]
#print axioms llpo_iff_bell_sign

-- ============================================================
-- STRATIFICATION
-- Expected: [propext, Classical.choice, Quot.sound, llpo_real_of_llpo]
-- ============================================================
#print axioms bell_stratification

-- ============================================================
-- HIERARCHY — No custom axioms
-- Expected: [propext, Classical.choice, Quot.sound]
-- ============================================================
#print axioms lpo_implies_wlpo
#print axioms wlpo_implies_llpo
#print axioms lpo_implies_llpo

-- ============================================================
-- ENCODED ASYMMETRY — No custom axioms
-- Expected: [propext, Classical.choice, Quot.sound]
-- ============================================================
#print axioms evenField_eq_zero_iff
#print axioms oddField_eq_zero_iff
#print axioms bellAsymmetry_nonpos_implies_even_false
#print axioms bellAsymmetry_nonneg_implies_odd_false

end Papers.P21
