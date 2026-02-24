/-
Papers/P14_Decoherence/CauchyModulus.lean
Paper 14: The Measurement Problem as a Logical Artefact.

The BISH content: explicit ε-approximation for quantum decoherence.

For any ε > 0, there is an explicitly computable N₀ such that the
coherence c(N) < ε for all N ≥ N₀. The bound is constructive:
N₀ depends only on the initial coherence, the interaction angle θ,
and the desired precision ε.

This is the minimum publishable result. The axiom certificate must be
clean: no Classical.choice beyond Mathlib infrastructure.
-/
import Papers.P14_Decoherence.MonotoneDecay

namespace Papers.P14

open Real

noncomputable section

-- ========================================================================
-- Trigonometric bounds for the interaction angle
-- ========================================================================

/-- For 0 < θ < π, the half-angle θ/2 lies in (0, π/2),
    so cos(θ/2) is strictly positive. -/
theorem cos_half_pos_of_angle {θ : ℝ} (hθ : 0 < θ ∧ θ < π) :
    0 < Real.cos (θ / 2) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · linarith [hθ.2]
  · linarith [hθ.1]

/-- For 0 < θ < π, cos(θ/2) < 1 (the cosine is strictly less than 1
    because θ/2 > 0). -/
theorem cos_half_lt_one_of_angle {θ : ℝ} (hθ : 0 < θ ∧ θ < π) :
    Real.cos (θ / 2) < 1 := by
  rw [← Real.cos_zero]
  exact Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) (by linarith [hθ.2]) (by linarith [hθ.1])

/-- For 0 < θ < π, |cos(θ/2)| < 1. -/
theorem abs_cos_half_lt_one {θ : ℝ} (hθ : 0 < θ ∧ θ < π) :
    |Real.cos (θ / 2)| < 1 := by
  rw [abs_of_pos (cos_half_pos_of_angle hθ)]
  exact cos_half_lt_one_of_angle hθ

-- ========================================================================
-- The BISH ε-bound
-- ========================================================================

/-- **Theorem (BISH ε-approximation for decoherence).**

    For any ε > 0, if 0 < θ < π (so each interaction produces genuine
    decoherence), then there exists an explicit N₀ such that for all
    N ≥ N₀, the coherence c(N) < ε.

    The proof constructs N₀ from the geometric decay formula
    c(N) = c₀ · r^N where r = |cos(θ/2)| < 1, using the Mathlib lemma
    `exists_pow_lt_of_lt_one` for the geometric bound.

    This is pure BISH: the witness N₀ is computable from θ, ε, and c₀.
    No limits, no completeness, no LPO. -/
theorem decoherence_epsilon_bound (ρ₀ : Matrix (Fin 2) (Fin 2) ℂ) (θ : ℝ)
    (hθ : 0 < θ ∧ θ < π)
    (hc : 0 < ‖ρ₀ 0 1‖)
    (ε : ℝ) (hε : ε > 0) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → coherence ρ₀ θ N < ε := by
  -- Set r = |cos(θ/2)| with 0 ≤ r < 1
  set r := |Real.cos (θ / 2)| with hr_def
  have hr_nonneg : 0 ≤ r := abs_nonneg _
  have hr_lt_one : r < 1 := abs_cos_half_lt_one hθ
  -- We need c₀ · r^N < ε, i.e., r^N < ε/c₀
  set c₀ := ‖ρ₀ 0 1‖ with hc₀_def
  have hc₀_pos : 0 < c₀ := hc
  -- Find N₀ such that r^N₀ < ε/c₀
  have hεc : 0 < ε / c₀ := div_pos hε hc₀_pos
  obtain ⟨N₀, hN₀⟩ := _root_.exists_pow_lt_of_lt_one hεc hr_lt_one
  -- For N ≥ N₀, r^N ≤ r^N₀ < ε/c₀, so c₀ · r^N < ε
  exact ⟨N₀, fun N hN => by
    rw [coherence_eq_geometric]
    calc c₀ * r ^ N
        ≤ c₀ * r ^ N₀ := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hc₀_pos)
          exact pow_le_pow_of_le_one hr_nonneg (le_of_lt hr_lt_one) hN
      _ < c₀ * (ε / c₀) := by
          apply mul_lt_mul_of_pos_left hN₀ hc₀_pos
      _ = ε := by
          field_simp⟩

/-- **Corollary:** When the initial state has zero off-diagonal coherence,
    the coherence is identically zero — trivially BISH. -/
theorem coherence_zero_of_diagonal (ρ₀ : Matrix (Fin 2) (Fin 2) ℂ) (θ : ℝ) (N : ℕ)
    (h : ρ₀ 0 1 = 0) :
    coherence ρ₀ θ N = 0 := by
  simp [coherence_eq_geometric, h, norm_zero]

end

end Papers.P14
