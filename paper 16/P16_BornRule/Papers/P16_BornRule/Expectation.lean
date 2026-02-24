/-
Papers/P16_BornRule/Expectation.lean
Paper 16: The Born Rule as a Logical Artefact.

Theorem 2: Quantum expectation value is BISH.
  - expectation_real: for Hermitian A, ⟨ψ, Aψ⟩ is real

All BISH — one inner product, one matrix-vector multiply.
-/
import Papers.P16_BornRule.BornProbability

namespace Papers.P16

open Complex Matrix Finset

-- ========================================================================
-- Expectation value of a Hermitian operator is real
-- ========================================================================

/-- For a Hermitian matrix A (A† = A), the expectation value ⟨ψ, Aψ⟩ is real:
    conj(⟨ψ, Aψ⟩) = ⟨Aψ, ψ⟩ = ⟨ψ, A†ψ⟩ = ⟨ψ, Aψ⟩.
    A complex number that equals its conjugate is real. -/
theorem expectation_real {d : ℕ} (ψ : Fin d → ℂ)
    (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.conjTranspose = A) :
    (expectationValue ψ A).im = 0 := by
  unfold expectationValue
  have h1 : cdot ψ (A.mulVec ψ) = cdot (A.mulVec ψ) ψ :=
    hermitian_cdot_swap ψ ψ A hA
  have h2 : cdot (A.mulVec ψ) ψ = starRingEnd ℂ (cdot ψ (A.mulVec ψ)) :=
    cdot_hermitian (A.mulVec ψ) ψ
  have h3 : cdot ψ (A.mulVec ψ) = starRingEnd ℂ (cdot ψ (A.mulVec ψ)) := h1.trans h2
  have h4 := Complex.ext_iff.mp h3
  simp only [Complex.conj_re, Complex.conj_im] at h4
  linarith [h4.2]

end Papers.P16
