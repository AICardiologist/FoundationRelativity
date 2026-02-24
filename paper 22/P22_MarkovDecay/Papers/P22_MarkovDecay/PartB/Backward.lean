/-
  Paper 22: Markov's Principle and the Constructive Cost of Eventual Decay
  PartB/Backward.lean — EventualDecay implies Markov's Principle (novel)

  Given an EventualDecay oracle, we extract a witness for any binary
  sequence α with ¬(∀n, α(n) = false):

  1. Construct encoded rate λ_α = Σ α(n) · (1/2)^(n+1)
  2. From ¬(∀n, false) and zero-iff: λ_α ≠ 0; also λ_α ≥ 0
  3. Apply EventualDecay with ε = 1/2: get T > 0 with exp(-λ_α·T) < 1/2
  4. From exp(-λ_α·T) < 1/2: deduce λ_α > 0 via exp/log chain
  5. Archimedean: find k₀ with (1/2)^k₀ < λ_α/2
  6. Tail bound: partialRate α k₀ > 0
  7. Bounded search: extract witness α(n) = true

  NOTE: EventualDecay is stated INLINE to avoid importing the axiom
  mp_real_of_mp (which lives in Forward.lean).
-/
import Papers.P22_MarkovDecay.Defs.Markov
import Papers.P22_MarkovDecay.Defs.Decay
import Papers.P22_MarkovDecay.Defs.EncodedRate

namespace Papers.P22

noncomputable section

-- ========================================================================
-- Helper: extract positivity from exp inequality
-- ========================================================================

/-- From survivalProb a T < 1/2 with T > 0 and a ≥ 0, deduce a > 0.
    If a = 0 then exp(0) = 1, contradicting < 1/2. -/
private theorem pos_of_exp_decay (a T : ℝ) (_hT : 0 < T) (hnn : 0 ≤ a)
    (h : survivalProb a T < 1 / 2) : 0 < a := by
  unfold survivalProb at h
  by_contra hle
  push_neg at hle
  -- If a ≤ 0 and a ≥ 0, then a = 0
  have ha0 : a = 0 := le_antisymm hle hnn
  -- Then exp(-(0 * T)) = exp(0) = 1, contradicting < 1/2
  rw [ha0] at h
  simp only [zero_mul, neg_zero, Real.exp_zero] at h
  linarith

-- ========================================================================
-- Main backward theorem
-- ========================================================================

/-- Theorem 5 (Backward / Novel): EventualDecay implies Markov's Principle.

    EventualDecay is stated inline to avoid importing the axiom
    mp_real_of_mp (which lives in Forward.lean). -/
theorem mp_of_eventualDecay
    (hed : ∀ (lambda_ : ℝ), 0 ≤ lambda_ → lambda_ ≠ 0 →
      ∀ (eps : ℝ), 0 < eps → eps < 1 →
        ∃ (T : ℝ), 0 < T ∧ survivalProb lambda_ T < eps) :
    MarkovPrinciple := by
  intro α hne
  -- Step 1-2: Construct encoded rate, derive nonzero
  have hlnn : 0 ≤ encodedRate α := encodedRate_nonneg α
  have hlne : encodedRate α ≠ 0 := by
    intro heq
    exact hne ((encodedRate_eq_zero_iff α).mp heq)
  -- Step 3: Apply EventualDecay with ε = 1/2
  obtain ⟨T, hTpos, hPlt⟩ := hed (encodedRate α) hlnn hlne (1 / 2)
    (by norm_num) (by norm_num)
  -- Step 4: Extract positivity from the exp inequality
  have hlpos : 0 < encodedRate α := pos_of_exp_decay (encodedRate α) T hTpos hlnn hPlt
  -- Step 5: Archimedean — find k₀ with (1/2)^k₀ < (encodedRate α)/2
  obtain ⟨k₀, hk₀⟩ : ∃ k₀, ((1 : ℝ) / 2) ^ k₀ < encodedRate α / 2 :=
    exists_pow_lt_of_lt_one (by linarith) (by norm_num)
  -- Step 6: Tail bound gives partialRate > 0
  have htail := encodedRate_sub_partialRate_le α k₀
  -- (1/2)^(k₀+1) ≤ (1/2)^k₀ (since 1/2 ≤ 1 and k₀ ≤ k₀+1)
  have hpow_le : ((1 : ℝ) / 2) ^ (k₀ + 1) ≤ ((1 : ℝ) / 2) ^ k₀ := by
    apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
    exact Nat.le_succ k₀
  -- partialRate ≥ encodedRate - (1/2)^(k₀+1) ≥ encodedRate - (1/2)^k₀
  -- > encodedRate - encodedRate/2 = encodedRate/2 > 0
  have hpartial_pos : 0 < partialRate α k₀ := by linarith
  -- Step 7: Bounded search — extract witness from positive partial sum
  exact witness_from_partial_sum_pos α k₀ hpartial_pos

end

-- Axiom audit: NO custom axioms (EventualDecay is a hypothesis)
-- Expected: [propext, Classical.choice, Quot.sound]
#print axioms mp_of_eventualDecay

end Papers.P22
