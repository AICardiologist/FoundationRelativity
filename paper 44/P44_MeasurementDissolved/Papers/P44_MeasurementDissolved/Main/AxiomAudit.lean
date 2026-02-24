/-
  Paper 44: The Measurement Problem Dissolved
  Main/AxiomAudit.lean — Axiom audit for all key theorems

  Following the programme convention (Papers 8, 14, 16, 23):
  every paper includes an axiom audit that displays the logical
  dependencies of all key theorems via #print axioms.

  Expected axioms:
  - propext, Quot.sound, Classical.choice (Mathlib infrastructure for ℝ)
  - sorry (for sorry'd proof obligations — transparently tracked)
  Note: bmc_of_lpo, lpo_of_bmc were changed from `axiom` to `theorem ... sorry`
  in revision per ITP convention (Referee 3 Issue 2).
-/
import Papers.P44_MeasurementDissolved.Main.Synthesis

namespace Papers.P44

-- ========================================================================
-- § 3 Copenhagen (WLPO) — Axiom audit
-- ========================================================================

section Copenhagen_Audit

#print axioms copenhagen_implies_WLPO
-- Expected: propext, Classical.choice, Quot.sound (from ℝ/tsum infrastructure)
-- NO sorry expected (fully proved)

#print axioms WLPO_implies_copenhagen
-- Expected: + sorry (reverse direction sorry'd)

#print axioms copenhagen_iff_WLPO

#print axioms strong_copenhagen_implies_LPO
-- Expected: propext, Classical.choice, Quot.sound (NO sorry — fully proved)

#print axioms strong_implies_weak
-- Expected: no sorry, minimal axioms

#print axioms copenhagen_spectrum
-- Expected: propext, Classical.choice, Quot.sound (NO sorry — all three fully proved)

end Copenhagen_Audit

-- ========================================================================
-- § 4 Many-Worlds (DC) — Axiom audit
-- ========================================================================

section ManyWorlds_Audit

#print axioms manyworlds_implies_DC
-- Expected: sorry (type encoding)

#print axioms DC_implies_manyworlds
-- Expected: propext, Quot.sound (NO sorry — fully proved in revision, no Classical.choice)

#print axioms manyworlds_iff_DC

-- Bonus: uniform case (no sorry expected)
#print axioms uniform_world_exists

-- Sigma-type witness (added in revision, no sorry expected)
#print axioms uniform_world_witness

end ManyWorlds_Audit

-- ========================================================================
-- § 5 Bohmian Mechanics (LPO) — Axiom audit
-- ========================================================================

section Bohmian_Audit

#print axioms trajectory_satisfies_ODE
-- Expected: sorry (pure calculus)

#print axioms bohmian_implies_LPO
-- Expected: sorry

#print axioms LPO_implies_bohmian
-- Expected: sorryAx + sorry (depends on bmc_of_lpo which is now sorry'd)

#print axioms bohmian_iff_LPO

#print axioms finite_time_bish
-- Expected: propext, Classical.choice, Quot.sound (NO sorry — delegates to bohmian_trajectory_zero)

end Bohmian_Audit

-- ========================================================================
-- § 6 Main result — Axiom audit
-- ========================================================================

section Main_Audit

#print axioms measurement_problem_dissolved
-- Expected: propext, Classical.choice, Quot.sound,
--           bmc_of_lpo, lpo_of_bmc, + sorry

#print axioms interpretation_hierarchy

end Main_Audit

-- ========================================================================
-- Logical principles — Axiom audit
-- ========================================================================

section Principles_Audit

#print axioms lpo_implies_wlpo
-- Expected: no sorry, no extra axioms beyond propext

#print axioms lpo_iff_bmc
-- Expected: bmc_of_lpo, lpo_of_bmc

end Principles_Audit

end Papers.P44
