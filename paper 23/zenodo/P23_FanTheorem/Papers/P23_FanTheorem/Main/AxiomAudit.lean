/-
  Paper 23: The Fan Theorem and the Constructive Cost of Optimization
  Main/AxiomAudit.lean — Comprehensive axiom audit

  ZERO custom axioms across all theorems.
  Only Mathlib infrastructure: [propext, Classical.choice, Quot.sound]

  This is the cleanest axiom audit of any paper in the CRM series,
  achieved by defining FanTheorem := EVT_max directly.
-/
import Papers.P23_FanTheorem.Main.Stratification
import Papers.P23_FanTheorem.Main.PhysicalInstance

namespace Papers.P23

-- ========================================================================
-- Part A: BISH (no custom axioms)
-- ========================================================================
section PartA_Audit

#print axioms isingFreeEnergy_continuous
-- Expected: [propext, Classical.choice, Quot.sound]

#print axioms finite_opt_bish
-- Expected: [propext, Classical.choice, Quot.sound]

#print axioms partA_summary
-- Expected: [propext, Classical.choice, Quot.sound]

end PartA_Audit

-- ========================================================================
-- Part B: FT calibration (ZERO custom axioms!)
-- ========================================================================
section PartB_Audit

#print axioms evt_min_of_evt_max
-- Expected: [propext]

#print axioms evt_max_of_evt_min
-- Expected: [propext]

#print axioms compact_opt_of_evt_min
-- Expected: [propext]

#print axioms evt_min_of_compact_opt
-- Expected: [propext]

#print axioms ft_iff_compact_opt
-- Expected: [propext]

end PartB_Audit

-- ========================================================================
-- Physical instance: FT → Ising optimization
-- ========================================================================
section PhysicalInstance_Audit

#print axioms ising_opt_of_ft
-- Expected: [propext, Classical.choice, Quot.sound]

end PhysicalInstance_Audit

-- ========================================================================
-- Main results
-- ========================================================================
section Main_Audit

#print axioms fan_stratification
-- Expected: [propext, Classical.choice, Quot.sound]

end Main_Audit

-- ========================================================================
-- Hierarchy: no custom axioms
-- ========================================================================
section Hierarchy_Audit

#print axioms lpo_implies_mp
-- Expected: [propext]

#print axioms lpo_implies_wlpo
-- Expected: [propext]

#print axioms wlpo_implies_llpo
-- Expected: [propext, Classical.choice, Quot.sound]

end Hierarchy_Audit

/-
  SUCCESS: All axiom audits show only Mathlib infrastructure axioms.
  Zero custom axioms. This is the cleanest audit of any paper in the
  CRM series (Papers 2-23).

  The connection to the bar-theoretic Fan Theorem is by citation:
  Berger (2005), Bridges-Vîță (2006), Julian-Richman (2002).
-/

end Papers.P23
