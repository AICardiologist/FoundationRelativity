/-
Papers/P19_WKBTunneling/Calibration/PartC.lean
Theorem 5: The full WKB computation for a general barrier (turning points +
semiclassical limit) is equivalent to LPO.

The full WKB assertion = TPP ∧ BMC.
  - TPP costs LLPO (Part B)
  - BMC ↔ LPO (Bridges-Vîță)
  - LPO ≥ LLPO, so the conjunction = LPO

Axiom audit expectation:
  [propext, Classical.choice, Quot.sound, exact_ivt_iff_llpo, bmc_iff_lpo]
-/
import Papers.P19_WKBTunneling.Calibration.PartB
import Papers.P19_WKBTunneling.WKB.Limit
import Papers.P19_WKBTunneling.Basic.Hierarchy

noncomputable section
namespace Papers.P19

-- ========================================================================
-- LPO → FullWKBGeneralBarrier
-- ========================================================================

/-- LPO implies the full WKB assertion.
    Step 1: LPO → LLPO → TPP (turning points exist).
    Step 2: LPO → BMC (bounded monotone convergence). -/
theorem lpo_implies_full_wkb : LPO → FullWKBGeneralBarrier := by
  intro hLPO
  constructor
  · -- TPP from LLPO
    exact turning_point_problem_iff_llpo.mpr (lpo_implies_llpo hLPO)
  · -- BMC from LPO
    exact bmc_iff_lpo.mpr hLPO

-- ========================================================================
-- FullWKBGeneralBarrier → LPO
-- ========================================================================

/-- The full WKB assertion implies LPO.
    The BMC component directly gives LPO via bmc_iff_lpo. -/
theorem full_wkb_implies_lpo : FullWKBGeneralBarrier → LPO := by
  intro ⟨_hTPP, hBMC⟩
  exact bmc_iff_lpo.mp hBMC

-- ========================================================================
-- Theorem 5: Full WKB ↔ LPO
-- ========================================================================

/-- Theorem 5: The full semiclassical tunneling computation for a general
    barrier — including both turning point identification and the ℏ → 0
    limit — is equivalent to LPO.

    The turning point problem alone costs LLPO (Theorem 4), but adding the
    semiclassical convergence (BMC) pushes the total to LPO. Since LPO ≥ LLPO,
    the conjunction TPP ∧ BMC is equivalent to just LPO. -/
theorem full_wkb_iff_lpo : FullWKBGeneralBarrier ↔ LPO :=
  ⟨full_wkb_implies_lpo, lpo_implies_full_wkb⟩

end Papers.P19
end
