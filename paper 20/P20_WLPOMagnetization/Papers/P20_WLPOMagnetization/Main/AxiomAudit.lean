/-
  Paper 20: WLPO Equivalence via Ising Magnetization Phase Classification
  Main/AxiomAudit.lean — Comprehensive axiom audit

  Three-tier decomposition verified by #print axioms:
    Part A (BISH): propext, Classical.choice, Quot.sound only
    Part B (WLPO): adds wlpo_real_of_wlpo
    Hierarchy:      propext, Classical.choice, Quot.sound only
-/
import Papers.P20_WLPOMagnetization.Main.Stratification

namespace Papers.P20

-- ============================================================
-- PART A: BISH — No custom axioms
-- Expected: [propext, Classical.choice, Quot.sound]
-- ============================================================
#print axioms mag_computable
#print axioms mag_zero_field

-- ============================================================
-- PART B: WLPO — One custom axiom
-- ============================================================

-- Forward (WLPO → PhaseClassification):
-- Expected: [propext, Classical.choice, Quot.sound, wlpo_real_of_wlpo]
#print axioms phase_classification_of_wlpo

-- Backward (PhaseClassification → WLPO):
-- Expected: [propext, Classical.choice, Quot.sound] — NO custom axioms
#print axioms wlpo_of_phase_classification

-- Main equivalence:
-- Expected: [propext, Classical.choice, Quot.sound, wlpo_real_of_wlpo]
#print axioms wlpo_iff_phase_classification

-- ============================================================
-- STRATIFICATION
-- Expected: [propext, Classical.choice, Quot.sound, wlpo_real_of_wlpo]
-- ============================================================
#print axioms ising_stratification

-- ============================================================
-- HIERARCHY — No custom axioms
-- Expected: [propext, Classical.choice, Quot.sound]
-- ============================================================
#print axioms lpo_implies_wlpo

-- ============================================================
-- ENCODED FIELD — No custom axioms
-- Expected: [propext, Classical.choice, Quot.sound]
-- ============================================================
#print axioms encodedField_eq_zero_iff

-- ============================================================
-- MAGNETIZATION ZERO-IFF — No custom axioms
-- Expected: [propext, Classical.choice, Quot.sound]
-- ============================================================
#print axioms magnetization_inf_eq_zero_iff

end Papers.P20
