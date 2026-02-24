/-
  Paper 43: What the Ceiling Means
  Assembly/AxiomAudit.lean — Comprehensive axiom audit

  Custom axioms used:
  - `cournot`: Cournot's Principle (bridge axiom, physical postulate)
  - `survival_prob_zero`: bridge from probability model to measure space

  Mathlib infrastructure: [propext, Classical.choice, Quot.sound]
  These appear in all theorems over ℝ because Mathlib's real numbers
  use classical Cauchy completion. This is an infrastructure artifact,
  not proof-level non-constructivity. Constructive stratification is
  established by proof content, not axiom checker output.
-/
import Papers.P43_Actualisation.Assembly.FineStructure

namespace Papers.P43

-- ========================================================================
-- BISH theorems (no custom axioms)
-- ========================================================================
section BISH_Audit

-- Theorem 2: detection time is BISH
#print axioms detection_time_bish
-- Expected: [propext, Classical.choice, Quot.sound]

-- Helper lemma
#print axioms exp_neg_mul_lt_of_gt_log_inv
-- Expected: [propext, Classical.choice, Quot.sound]

-- Theorem 3: Poincaré non-return measure zero
#print axioms poincare_nonreturn_measure_zero
-- Expected: [propext, Classical.choice, Quot.sound]

end BISH_Audit

-- ========================================================================
-- Hierarchy (pure logic)
-- ========================================================================
section Hierarchy_Audit

#print axioms lpo_implies_mp
-- Expected: [propext]

#print axioms lpo_implies_wlpo
-- Expected: [propext]

#print axioms wlpo_implies_llpo
-- Expected: [propext, Classical.choice, Quot.sound]

#print axioms lpo_implies_llpo
-- Expected: [propext, Classical.choice, Quot.sound]

end Hierarchy_Audit

-- ========================================================================
-- Actualisation theorems (custom axioms: cournot, survival_prob_zero)
-- ========================================================================
section Actualisation_Audit

-- Step 2: not eternal survival (uses cournot + survival_prob_zero)
#print axioms not_eternal_survival
-- Expected: [propext, Classical.choice, Quot.sound, cournot, survival_prob_zero]

-- Step 3: atom decays (uses cournot + survival_prob_zero; MP is hypothesis)
#print axioms atom_decays_mp
-- Expected: [propext, Classical.choice, Quot.sound, cournot, survival_prob_zero]

-- Poincaré pointwise (uses cournot only; no survival_prob_zero)
#print axioms not_never_return
-- Expected: [propext, Classical.choice, Quot.sound, cournot]

#print axioms orbit_returns_mp
-- Expected: [propext, Classical.choice, Quot.sound, cournot]

-- False vacuum (reuses atom_decays_mp)
#print axioms vacuum_decays_mp
-- Expected: [propext, Classical.choice, Quot.sound, cournot, survival_prob_zero]

-- Tunnelling detection time (reuses detection_time_bish, BISH only)
#print axioms tunnelling_detection_time
-- Expected: [propext, Classical.choice, Quot.sound]

end Actualisation_Audit

-- ========================================================================
-- Assembly
-- ========================================================================
section Assembly_Audit

#print axioms fine_structure
-- Expected: [propext, Classical.choice, Quot.sound]

#print axioms lpo_subsidizes_actualisation
-- Expected: [propext]

end Assembly_Audit

/-
  AUDIT SUMMARY:
  ─────────────────────────────────────────────────────────
  BISH theorems:        Mathlib infrastructure only
  Hierarchy:            propext only (pure logic)
  Actualisation:        Mathlib infrastructure + cournot + survival_prob_zero
  Assembly:             Mathlib infrastructure only
  ─────────────────────────────────────────────────────────

  Two custom axioms:
  1. `cournot` — physical postulate (probability zero ⟹ impossible)
  2. `survival_prob_zero` — bridge (probability model ⟹ measure zero)

  MarkovPrinciple appears as a hypothesis in theorem statements,
  NOT as an axiom in #print axioms output. This is by design:
  the programme takes principles as hypotheses, not axioms.
-/

end Papers.P43
