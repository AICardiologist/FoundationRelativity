/-
Papers/P16_BornRule/BornProbability.lean
Paper 16: The Born Rule as a Logical Artefact.

Theorem 1: Born probability distribution is BISH.
  - cdot_hermitian: ⟨ψ, φ⟩ = conj(⟨φ, ψ⟩)
  - cnorm_sq_nonneg: ‖ψ‖² ≥ 0
  - born_prob_nonneg: 0 ≤ p_i (each Born probability is non-negative)
  - born_prob_sum_one: ∑ p_i = 1 (probabilities sum to 1)

All BISH — finite sums, matrix algebra, no limits, no choice.
-/
import Papers.P16_BornRule.Defs

namespace Papers.P16

open Finset Complex Matrix

-- ========================================================================
-- Helper: Re(∑ f i) = ∑ Re(f i)
-- ========================================================================

theorem re_sum {ι : Type*} {s : Finset ι} {f : ι → ℂ} :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => simp [Finset.sum_cons, ih]

-- ========================================================================
-- Hermitian symmetry of cdot
-- ========================================================================

/-- The complex inner product satisfies ⟨ψ, φ⟩ = conj(⟨φ, ψ⟩). -/
theorem cdot_hermitian {d : ℕ} (ψ φ : Fin d → ℂ) :
    cdot ψ φ = starRingEnd ℂ (cdot φ ψ) := by
  unfold cdot
  rw [map_sum]
  congr 1; ext i
  simp [map_mul, mul_comm]

-- ========================================================================
-- Self inner product is real and non-negative
-- ========================================================================

/-- cnorm_sq is non-negative: ‖ψ‖² = Σ |ψ_i|² ≥ 0. -/
theorem cnorm_sq_nonneg {d : ℕ} (ψ : Fin d → ℂ) :
    0 ≤ cnorm_sq ψ := by
  unfold cnorm_sq cdot
  rw [re_sum]
  apply Finset.sum_nonneg
  intro i _
  have : starRingEnd ℂ (ψ i) * ψ i = ↑(Complex.normSq (ψ i)) := by
    rw [Complex.normSq_eq_conj_mul_self]
  rw [this, Complex.ofReal_re]
  exact Complex.normSq_nonneg _

-- ========================================================================
-- Hermitian swap at the sum level
-- ========================================================================

/-- For a Hermitian matrix P (P† = P):
    ⟨u, Pv⟩ = ⟨Pu, v⟩ (Hermitian property). -/
theorem hermitian_cdot_swap {d : ℕ} (u v : Fin d → ℂ)
    (P : Matrix (Fin d) (Fin d) ℂ) (hH : P.conjTranspose = P) :
    cdot u (P.mulVec v) = cdot (P.mulVec u) v := by
  unfold cdot mulVec dotProduct
  simp only [Finset.mul_sum, map_sum, map_mul]
  -- RHS is ∑ x, (∑ x_1, conj(P x x_1) * conj(u x_1)) * v x
  -- Push * v x inside: ∑ x, ∑ x_1, conj(P x x_1) * conj(u x_1) * v x
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1; ext j; congr 1; ext k
  have hPjk : starRingEnd ℂ (P j k) = P k j := by
    have h1 := congr_fun₂ hH k j
    simp only [conjTranspose_apply, star_def] at h1
    exact h1
  rw [hPjk]; ring

-- ========================================================================
-- Born probability: non-negativity
-- ========================================================================

/-- Born probability for each eigenvalue is non-negative.
    Proof: bornProb = Re(⟨ψ, Pψ⟩) = Re(⟨Pψ, Pψ⟩) = ‖Pψ‖² ≥ 0.
    Uses P² = P and P† = P. -/
theorem born_prob_nonneg {d : ℕ} (ψ : Fin d → ℂ) (spec : SpectralDecomp d)
    (i : Fin d) :
    0 ≤ bornProb ψ spec i := by
  unfold bornProb
  suffices h : (cdot ψ ((spec.projections i).mulVec ψ)).re =
    cnorm_sq ((spec.projections i).mulVec ψ) from h ▸ cnorm_sq_nonneg _
  unfold cnorm_sq
  congr 1
  -- ⟨ψ, Pψ⟩ = ⟨ψ, P(Pψ)⟩ = ⟨Pψ, Pψ⟩  (using P²=P then P†=P)
  set Pi := spec.projections i with hPi_def
  have hP2 : Pi.mulVec (Pi.mulVec ψ) = Pi.mulVec ψ := by
    have hPP := spec.is_projection i  -- P * P = P
    rw [Matrix.mulVec_mulVec, hPP]
  conv_lhs =>
    rw [show Pi.mulVec ψ = Pi.mulVec (Pi.mulVec ψ) from hP2.symm]
  exact hermitian_cdot_swap ψ (Pi.mulVec ψ) Pi (spec.is_hermitian i)

-- ========================================================================
-- Born probability: sum to one
-- ========================================================================

/-- Born probabilities sum to 1 for a normalized state.
    Uses completeness: ∑ P_i = I, so ∑ ⟨ψ, P_i ψ⟩ = ⟨ψ, ψ⟩ = ‖ψ‖².
    When ‖ψ‖² = 1, the sum is 1. -/
theorem born_prob_sum_one {d : ℕ} (ψ : Fin d → ℂ) (spec : SpectralDecomp d)
    (hψ : cnorm_sq ψ = 1) :
    ∑ i : Fin d, bornProb ψ spec i = 1 := by
  unfold bornProb
  rw [← re_sum]
  -- Linearity: ∑ cdot ψ (P_i ψ) = cdot ψ ((∑ P_i) ψ)
  have lin : ∑ i : Fin d, cdot ψ ((spec.projections i).mulVec ψ) =
    cdot ψ ((∑ i : Fin d, spec.projections i).mulVec ψ) := by
    unfold cdot
    rw [Finset.sum_comm]
    congr 1; ext j
    rw [← Finset.mul_sum]
    congr 1
    simp only [sum_mulVec, Finset.sum_apply]
  rw [lin, spec.is_complete, Matrix.one_mulVec]
  exact hψ

end Papers.P16
