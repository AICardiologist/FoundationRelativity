/-
Papers/P14_Decoherence/MonotoneDecay.lean
Paper 14: The Measurement Problem as a Logical Artefact.

Monotonicity and boundedness of the coherence sequence:
  - Coherence is antitone (non-increasing): c(N+1) ≤ c(N)
  - Coherence is bounded below by 0
  - Coherence is bounded above by c(0)

These properties establish that the coherence sequence is a bounded
monotone (decreasing) sequence — the type of sequence whose convergence
is equivalent to BMC, hence to LPO.
-/
import Papers.P14_Decoherence.FiniteDecoherence

namespace Papers.P14

noncomputable section

-- ========================================================================
-- Coherence is non-negative
-- ========================================================================

/-- Coherence is non-negative (it is the absolute value of a complex number). -/
theorem coherence_nonneg (ρ₀ : Matrix (Fin 2) (Fin 2) ℂ) (θ : ℝ) (N : ℕ) :
    0 ≤ coherence ρ₀ θ N := by
  simp only [coherence]
  exact norm_nonneg _

-- ========================================================================
-- Coherence is antitone
-- ========================================================================

/-- Coherence is antitone (non-increasing) when |cos(θ/2)| ≤ 1.

    Proof: c(N) = c₀ · r^N where r = |cos(θ/2)| ≤ 1 and c₀ ≥ 0.
    Since r^(N+1) = r^N · r ≤ r^N when 0 ≤ r ≤ 1, the sequence is antitone. -/
theorem coherence_antitone (ρ₀ : Matrix (Fin 2) (Fin 2) ℂ) (θ : ℝ)
    (hcos : |Real.cos (θ / 2)| ≤ 1) :
    Antitone (coherence ρ₀ θ) := by
  intro m n hmn
  simp only [coherence_eq_geometric]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact pow_le_pow_of_le_one (abs_nonneg _) hcos hmn

/-- Coherence is bounded above by the initial coherence. -/
theorem coherence_le_initial (ρ₀ : Matrix (Fin 2) (Fin 2) ℂ) (θ : ℝ)
    (hcos : |Real.cos (θ / 2)| ≤ 1) (N : ℕ) :
    coherence ρ₀ θ N ≤ coherence ρ₀ θ 0 :=
  coherence_antitone ρ₀ θ hcos (Nat.zero_le N)

end

end Papers.P14
