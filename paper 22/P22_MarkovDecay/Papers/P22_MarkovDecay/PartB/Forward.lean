/-
  Paper 22: Markov's Principle and the Constructive Cost of Eventual Decay
  PartB/Forward.lean — Markov's Principle implies EventualDecay

  Given MP, we can convert λ ≠ 0 (with λ ≥ 0) to an explicit lower bound
  q > 0, then use Part A's detection time.

  Uses ε/2 trick: detection_time_works gives ≤ ε/2, hence < ε.
-/
import Papers.P22_MarkovDecay.PartA.DetectionTime
import Papers.P22_MarkovDecay.Defs.Markov

namespace Papers.P22

/-- Interface axiom: MP for sequences implies MP for non-negative reals.
    Standard (Bridges-Richman 1987, Bridges-Vita 2006).

    For x ≥ 0 with x ≠ 0, MP produces a rational lower bound q > 0
    with q ≤ x. -/
axiom mp_real_of_mp :
  MarkovPrinciple →
    ∀ (x : ℝ), 0 ≤ x → x ≠ 0 → ∃ (q : ℚ), (0 < (q : ℝ)) ∧ (q : ℝ) ≤ x

/-- Theorem 4 (Forward): MP implies EventualDecay.
    Given MP, any non-negative nonzero decay rate λ eventually produces
    survival probability below any threshold ε ∈ (0,1). -/
theorem eventualDecay_of_mp (hmp : MarkovPrinciple) : EventualDecay := by
  intro lambda_ hlnn hlne eps heps heps1
  -- Step 1: MP gives an explicit positive lower bound
  obtain ⟨q, hqpos, hqle⟩ := mp_real_of_mp hmp lambda_ hlnn hlne
  -- Step 2: Use detection time with half-threshold for strict inequality
  have heps2 : 0 < eps / 2 := by linarith
  have heps2_1 : eps / 2 < 1 := by linarith
  exact ⟨detectionTime (eps / 2) q,
    detectionTime_pos q (eps / 2) hqpos heps2 heps2_1,
    calc survivalProb lambda_ (detectionTime (eps / 2) q)
        ≤ eps / 2 := detection_time_works lambda_ q (eps / 2) hqpos hqle heps2 heps2_1
      _ < eps := by linarith⟩

-- Axiom audit: uses mp_real_of_mp
-- Expected: [propext, Classical.choice, Quot.sound, mp_real_of_mp]
#print axioms eventualDecay_of_mp

end Papers.P22
