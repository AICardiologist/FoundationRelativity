/-
Papers/P19_WKBTunneling/Main.lean
The Logical Cost of Quantum Tunneling: LLPO and WKB Turning Points

Paper 19 in the Constructive Reverse Mathematics series.
Paul C.-K. Lee, February 2026.

Main results:
  - Theorem 1 (Part A): Specific barriers with known turning points are BISH-computable.
  - Theorem 4 (Part B): The Turning Point Problem ↔ LLPO (first physical LLPO calibration).
  - Theorem 5 (Part C): Full WKB for general barriers ↔ LPO.
  - Theorem 6: Dispensability — specific barriers need no omniscience principles.

Three-tier decomposition: BISH (computation) / LLPO (turning points) / LPO (semiclassical limit).
-/
import Papers.P19_WKBTunneling.Calibration.PartA
import Papers.P19_WKBTunneling.Calibration.PartB
import Papers.P19_WKBTunneling.Calibration.PartC
import Papers.P19_WKBTunneling.Calibration.Dispensability
import Papers.P19_WKBTunneling.Basic.Hierarchy

namespace Papers.P19

-- ========================================================================
-- Axiom audits
-- ========================================================================

-- Part A: BISH — expected: [propext, Classical.choice, Quot.sound]
-- NO custom axioms (no exact_ivt_iff_llpo, no bmc_iff_lpo)
#print axioms wkb_action_computable
#print axioms tunneling_amplitude_computable

-- Part B: LLPO — expected: [..., exact_ivt_iff_llpo]
-- The single custom axiom certifies LLPO-level cost.
#print axioms turning_point_problem_iff_llpo

-- Part C: LPO — expected: [..., exact_ivt_iff_llpo, bmc_iff_lpo]
-- Both custom axioms certify LPO-level cost.
#print axioms full_wkb_iff_lpo

-- Dispensability: BISH — expected: [propext, Classical.choice, Quot.sound]
-- NO custom axioms.
#print axioms specific_barrier_dispensable

-- Hierarchy proofs
#print axioms lpo_implies_wlpo
#print axioms lpo_implies_llpo
#print axioms wlpo_implies_llpo

-- Specific barriers (Part A corollaries)
#print axioms rectangular_wkb_computable
#print axioms parabolic_wkb_computable

-- Parabolic turning point verification
#print axioms parabolicV_at_right_tp
#print axioms parabolicV_at_left_tp

end Papers.P19
