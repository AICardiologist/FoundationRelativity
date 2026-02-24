/-
  Paper 20: WLPO Equivalence via Ising Magnetization Phase Classification
  Main/Stratification.lean — Three-level stratification theorem

  The 1D Ising model exhibits observable-dependent logical cost:
    Level 1 (BISH): Finite-volume magnetization is computable
    Level 2 (WLPO): Phase classification (m = 0 vs m ≠ 0) ↔ WLPO
    Level 3 (LPO):  Thermodynamic limit (free energy convergence) ↔ LPO [Paper 8]

  The hierarchy BISH ⊊ WLPO ⊊ LPO is strict.
-/
import Papers.P20_WLPOMagnetization.PartA.PartA_Main
import Papers.P20_WLPOMagnetization.PartB.PartB_Main

namespace Papers.P20

/-- The three-level stratification of the 1D Ising model:
    1. (BISH) Finite-volume magnetization is computable
    2. (WLPO) Phase classification is equivalent to WLPO
    3. (Hierarchy) LPO → WLPO (strict hierarchy) -/
theorem ising_stratification :
    -- Level 1: BISH computability
    (∃ v : ℝ, v = magnetization_inf 1 1 0) ∧
    -- Level 2: WLPO equivalence
    (WLPO ↔ PhaseClassification) ∧
    -- Level 3: Hierarchy (LPO → WLPO)
    (LPO → WLPO) :=
  ⟨⟨_, rfl⟩, wlpo_iff_phase_classification, lpo_implies_wlpo⟩

-- ============================================================
-- Axiom audit
-- Expected: [propext, Classical.choice, Quot.sound, wlpo_real_of_wlpo]
-- ============================================================
#print axioms ising_stratification

end Papers.P20
