/-
  Paper 20: WLPO Equivalence via Ising Magnetization Phase Classification
  PartB/PartB_Main.lean — Main equivalence: WLPO ↔ Phase Classification

  Combines the forward direction (WLPO → PhaseClassification)
  with the backward direction (PhaseClassification → WLPO).
-/
import Papers.P20_WLPOMagnetization.PartB.Forward
import Papers.P20_WLPOMagnetization.PartB.Backward

namespace Papers.P20

/-- Theorem 5 (Main equivalence):
    WLPO is equivalent to the phase classification of the 1D Ising model.

    This is the central result of Paper 20:
    deciding whether m(∞, β, J, h) = 0 or ≠ 0 has exactly
    the logical strength of WLPO. -/
theorem wlpo_iff_phase_classification :
    WLPO ↔ PhaseClassification :=
  ⟨phase_classification_of_wlpo, wlpo_of_phase_classification⟩

-- ============================================================
-- Axiom audit
-- Expected: [propext, Classical.choice, Quot.sound, wlpo_real_of_wlpo]
-- ============================================================
#print axioms wlpo_iff_phase_classification

end Papers.P20
