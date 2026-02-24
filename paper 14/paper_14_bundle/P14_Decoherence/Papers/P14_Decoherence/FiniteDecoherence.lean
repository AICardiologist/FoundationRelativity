/-
Papers/P14_Decoherence/FiniteDecoherence.lean
Paper 14: The Measurement Problem as a Logical Artefact.

N-step iteration of the decoherence map:
  - Off-diagonal elements after N steps: ρ₀ 0 1 * cos(θ/2)^N
  - Geometric decay formula for coherence
  - Diagonal preservation under iteration

All proofs by induction on N. The key lemma decoherenceMap_01 has no
hypotheses on ρ (the formula is purely algebraic), which is essential
for the inductive step.
-/
import Papers.P14_Decoherence.DecoherenceMap

namespace Papers.P14

open Matrix

noncomputable section

-- ========================================================================
-- N-step iteration: off-diagonal elements
-- ========================================================================

/-- After N decoherence steps, the (0,1) entry is multiplied by cos(θ/2)^N.
    This is the fundamental geometric decay formula. -/
theorem decoherence_iterate_offdiag (θ : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) (N : ℕ) :
    ((decoherenceMap θ)^[N] ρ) 0 1 = ρ 0 1 * (↑(Real.cos (θ / 2)))^N := by
  induction N with
  | zero => simp [Function.iterate_zero]
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp_apply, decoherenceMap_01]
    rw [ih]
    ring

/-- After N decoherence steps, the (1,0) entry is multiplied by cos(θ/2)^N. -/
theorem decoherence_iterate_10 (θ : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) (N : ℕ) :
    ((decoherenceMap θ)^[N] ρ) 1 0 = ρ 1 0 * (↑(Real.cos (θ / 2)))^N := by
  induction N with
  | zero => simp [Function.iterate_zero]
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp_apply, decoherenceMap_10]
    rw [ih]
    ring

-- ========================================================================
-- N-step iteration: diagonal elements
-- ========================================================================

/-- Diagonal (0,0) entry is preserved under N decoherence steps. -/
theorem decoherence_iterate_00 (θ : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) (N : ℕ) :
    ((decoherenceMap θ)^[N] ρ) 0 0 = ρ 0 0 := by
  induction N with
  | zero => simp [Function.iterate_zero]
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp_apply, decoherenceMap_00]
    exact ih

/-- Diagonal (1,1) entry is preserved under N decoherence steps. -/
theorem decoherence_iterate_11 (θ : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) (N : ℕ) :
    ((decoherenceMap θ)^[N] ρ) 1 1 = ρ 1 1 := by
  induction N with
  | zero => simp [Function.iterate_zero]
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp_apply, decoherenceMap_11]
    exact ih

-- ========================================================================
-- Geometric decay formula for coherence
-- ========================================================================

/-- The coherence after N steps follows geometric decay:
    c(N) = |ρ₀ 0 1| · |cos(θ/2)|^N.

    This is the central formula connecting the decoherence map to
    exponential decay of quantum coherence. -/
theorem coherence_eq_geometric (ρ₀ : Matrix (Fin 2) (Fin 2) ℂ) (θ : ℝ) (N : ℕ) :
    coherence ρ₀ θ N = ‖ρ₀ 0 1‖ * |Real.cos (θ / 2)|^N := by
  simp only [coherence, decoherence_iterate_offdiag]
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]

end

end Papers.P14
