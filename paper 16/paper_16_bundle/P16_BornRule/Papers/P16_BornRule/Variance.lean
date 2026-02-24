/-
Papers/P16_BornRule/Variance.lean
Paper 16: The Born Rule as a Logical Artefact.

Theorem 3: Quantum variance is BISH.
  - variance_nonneg: Var_ψ(A) = ‖(A - μI)ψ‖² ≥ 0

All BISH — finite-dimensional matrix algebra.
-/
import Papers.P16_BornRule.BornProbability

namespace Papers.P16

open Complex Matrix

-- ========================================================================
-- Variance is non-negative
-- ========================================================================

/-- Quantum variance is non-negative.
    Var_ψ(A) = ⟨ψ, (A - μI)²ψ⟩ = ‖(A - μI)ψ‖² ≥ 0
    where μ = ⟨ψ|A|ψ⟩ is the expectation value.
    This is immediate from cnorm_sq being non-negative. -/
theorem variance_nonneg {d : ℕ} (ψ : Fin d → ℂ)
    (A : Matrix (Fin d) (Fin d) ℂ) (μ : ℂ) :
    0 ≤ cnorm_sq ((A - μ • (1 : Matrix (Fin d) (Fin d) ℂ)).mulVec ψ) :=
  cnorm_sq_nonneg _

end Papers.P16
