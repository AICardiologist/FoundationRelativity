/-
  Paper 43: What the Ceiling Means
  Assembly/FineStructure.lean — The fine structure of BISH+LPO

  The calibration table is a partial order with physical annotations:

              LPO
         (thermodynamic limits:
          Fekete, phase transitions,
          spectral gaps, condensates)
             /    \
          WLPO     MP
      (phase ID)  (actualisation:
                   Cournot + ¬∀ → ∃,
                   decay, recurrence,
                   tunnelling)
             \    /
              LLPO
          (Bell, KS, IVT,
           quantum foundations)
              |
             BISH
         (all mathematical
          predictions: probabilities,
          energies, cross-sections,
          detection times, spectra)

  Three universal mechanisms:
  | Principle | Mechanism                | Physical context          |
  |-----------|--------------------------|---------------------------|
  | LPO       | Fekete's subadditive     | Finite → infinite volume  |
  | LLPO      | Intermediate value thm   | Root-finding, measurement |
  | MP        | Cournot + ¬∀ → ∃        | Probability → actuality   |
-/
import Papers.P43_Actualisation.Hierarchy.LPOImpliesMP
import Papers.P43_Actualisation.BISHContent.ExponentialWitness
import Papers.P43_Actualisation.BISHContent.PoincareMeasure
import Papers.P43_Actualisation.Actualisation.RadioactiveDecay
import Papers.P43_Actualisation.Actualisation.PoincarePointwise
import Papers.P43_Actualisation.Actualisation.FalseVacuum

namespace Papers.P43

noncomputable section

open Real

-- ========================================================================
-- The fine structure: hierarchy + BISH content
-- ========================================================================

/-- The fine structure of the BISH+LPO ceiling.
    1. Hierarchy: LPO → WLPO, LPO → MP, WLPO → LLPO
    2. BISH content: detection time is computable (Theorem 2) -/
theorem fine_structure :
    -- Hierarchy
    (LPO → WLPO) ∧
    (LPO → MarkovPrinciple) ∧
    (WLPO → LLPO) ∧
    -- BISH content: detection time is computable
    (∀ rate ε : ℝ, 0 < rate → 0 < ε → ε < 1 →
      let t₀ := detectionTime rate ε
      0 < t₀ ∧ exp (-rate * t₀) < ε) :=
  ⟨lpo_implies_wlpo, lpo_implies_mp, wlpo_implies_llpo,
   fun rate ε hr hε hε1 => detection_time_bish rate ε hr hε hε1⟩

-- ========================================================================
-- LPO subsidizes actualisation
-- ========================================================================

/-- The ceiling automatically subsidizes MP.
    LPO (needed for thermodynamic limits) implies MP (needed for
    actualisation). Therefore the ceiling does not extend when
    we add actualisation. -/
theorem lpo_subsidizes_actualisation :
    LPO → MarkovPrinciple :=
  lpo_implies_mp

-- ========================================================================
-- Three readings of the ceiling
-- ========================================================================

-- Reading 1 (Strict Bishopian):
--   Physics = computable predictions only.
--   Logical constitution = BISH alone. LPO is idealisation cost.
--
-- Reading 2 (Standard, Paper 40):
--   Physics = predictions + thermodynamic limits.
--   Logical constitution = BISH + LPO. MP subsumed.
--
-- Reading 3 (Inclusive):
--   Physics = predictions + limits + actualisation.
--   Logical constitution = BISH + LPO + MP = BISH + LPO.
--   MP content is present but not independent.

-- All three readings use the same measurements.
-- The programme does not choose between them.

end

end Papers.P43
