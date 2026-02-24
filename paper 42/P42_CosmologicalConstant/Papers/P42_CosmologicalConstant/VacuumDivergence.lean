/-
  Paper 42: The Worst Prediction in Physics Is Not a Prediction
  VacuumDivergence.lean: Theorem 1 — The unregularized mode sum diverges

  The vacuum energy mode sum E_N = ½ Σ_{|k|≤N} √(k² + m²) is unbounded.
  Therefore no BMC limit exists: the "continuum vacuum energy"
  is not a real number at any level of the constructive hierarchy.
  This is a BISH proof (no omniscience principles needed).
-/
import Papers.P42_CosmologicalConstant.Defs

noncomputable section

-- ============================================================
-- Theorem 1: The unregularized vacuum energy diverges
-- ============================================================

/-- THEOREM 1: The unregularized vacuum energy mode sum diverges.
    The partial sums E_N are unbounded, so no limit L exists.
    The "continuum vacuum energy" is not a real number — not at BISH,
    not at LPO, not at any level. A divergent series has no BMC limit.

    Proof: Suppose for contradiction that E_N → L. Then for ε = 1,
    there exists N₀ with |E_N - L| < 1 for all N ≥ N₀.
    But mode_sum_unbounded gives N₁ with E_{N₁} > L + 1.
    Taking N = max(N₀, N₁): |E_N - L| < 1 but E_N > L + 1. Contradiction.

    BISH: the proof uses only the unboundedness axiom and basic arithmetic.
    No LPO, no BMC, no choice principles. -/
theorem vacuum_energy_divergent (m : ℝ) (hm : 0 ≤ m) :
    ¬ ∃ L : ℝ, ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → |mode_sum_partial m N - L| < ε := by
  intro ⟨L, hconv⟩
  -- Get N₁ with E_{N₁} > L + 1 from unboundedness
  obtain ⟨N₁, hN₁⟩ := mode_sum_unbounded m hm (L + 1)
  -- Get N₀ with |E_N - L| < 1 for all N ≥ N₀ from convergence
  obtain ⟨N₀, hN₀⟩ := hconv 1 one_pos
  -- Take N = max(N₀, N₁)
  have hN := hN₀ (max N₀ N₁) (le_max_left N₀ N₁)
  -- E_{max} > L + 1 from monotonicity
  have hbig : mode_sum_partial m (max N₀ N₁) > L + 1 :=
    lt_of_lt_of_le hN₁ (mode_sum_mono m hm (le_max_right N₀ N₁))
  -- |E_{max} - L| < 1 but E_{max} - L > 1 — contradiction
  linarith [abs_lt.mp hN]

/-- Corollary: the vacuum energy mode sum is not Cauchy.
    A divergent sequence has no Cauchy modulus. -/
theorem vacuum_energy_not_cauchy (m : ℝ) (hm : 0 ≤ m) :
    ¬ ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ M N : ℕ, N₀ ≤ M → N₀ ≤ N →
        |mode_sum_partial m M - mode_sum_partial m N| < ε := by
  intro hcauchy
  -- A Cauchy sequence is bounded
  obtain ⟨N₀, hN₀⟩ := hcauchy 1 one_pos
  -- All terms beyond N₀ are within 1 of a_{N₀}
  have hbdd : ∀ N : ℕ, N₀ ≤ N →
      mode_sum_partial m N < mode_sum_partial m N₀ + 1 := by
    intro N hN
    have := hN₀ N₀ N le_rfl hN
    linarith [abs_lt.mp this]
  -- But the sequence is unbounded
  obtain ⟨N₁, hN₁⟩ := mode_sum_unbounded m hm (mode_sum_partial m N₀ + 1)
  have := hbdd (max N₀ N₁) (le_max_left _ _)
  have : mode_sum_partial m (max N₀ N₁) > mode_sum_partial m N₀ + 1 :=
    lt_of_lt_of_le hN₁ (mode_sum_mono m hm (le_max_right _ _))
  linarith

end
