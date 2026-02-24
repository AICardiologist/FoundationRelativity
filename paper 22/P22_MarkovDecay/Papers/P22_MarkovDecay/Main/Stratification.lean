/-
  Paper 22: Markov's Principle and the Constructive Cost of Eventual Decay
  Main/Stratification.lean — Three-level stratification theorem

  Level 1 (BISH): Detection with known bounds
  Level 2 (MP):   EventualDecay ↔ MarkovPrinciple
  Level 3:        LPO → MP (hierarchy placement)
-/
import Papers.P22_MarkovDecay.PartA.PartA_Main
import Papers.P22_MarkovDecay.PartB.PartB_Main
import Papers.P22_MarkovDecay.Main.Hierarchy

namespace Papers.P22

/-- The three-level stratification of radioactive decay:
    - BISH: detection with explicit bounds
    - MP: eventual decay ↔ Markov's Principle
    - Hierarchy: LPO implies MP -/
theorem decay_stratification :
    -- Level 1 (BISH): detection time works for known bounds
    (∀ lambda_ q eps : ℝ, 0 < q → q ≤ lambda_ → 0 < eps → eps < 1 →
      survivalProb lambda_ (detectionTime eps q) ≤ eps) ∧
    -- Level 2 (MP): main equivalence
    (MarkovPrinciple ↔ EventualDecay) ∧
    -- Level 3 (Hierarchy): LPO implies MP
    (LPO → MarkovPrinciple) :=
  ⟨fun lambda_ q eps => detection_time_works lambda_ q eps,
   mp_iff_eventualDecay,
   mp_of_lpo⟩

-- Axiom audit
-- Expected: [propext, Classical.choice, Quot.sound, mp_real_of_mp]
#print axioms decay_stratification

end Papers.P22
