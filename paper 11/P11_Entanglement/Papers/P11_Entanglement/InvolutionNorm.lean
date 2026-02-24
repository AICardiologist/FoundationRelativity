/-
Papers/P11_Entanglement/InvolutionNorm.lean
Paper 11: Constructive Cost of Quantum Entanglement — CRM over Mathlib.

Dot-product norm-preservation: tensoring with a self-adjoint involution
preserves the dot-product norm ‖v‖² := star v ⬝ᵥ v.

Key result: star ((A ⊗ M) *ᵥ v) ⬝ᵥ ((A ⊗ M) *ᵥ v) =
            star ((I ⊗ M) *ᵥ v) ⬝ᵥ ((I ⊗ M) *ᵥ v) when A² = I, Aᴴ = A.

All proofs are purely algebraic (dotProduct, mulVec, vecMul) — BISH-valid.
-/
import Papers.P11_Entanglement.KroneckerLemmas

namespace Papers.P11

open scoped Matrix Kronecker
open Matrix

noncomputable section

-- ========================================================================
-- Unitary dot-product preservation
-- ========================================================================

/-- When UᴴU = I, star (U *ᵥ w) ⬝ᵥ (U *ᵥ w) = star w ⬝ᵥ w.
    This is the algebraic core of unitary norm preservation.

    Proof: star(U*ᵥw) = star w ᵥ* Uᴴ, and
    (star w ᵥ* Uᴴ) ⬝ᵥ (U *ᵥ w) = star w ⬝ᵥ (UᴴU *ᵥ w) = star w ⬝ᵥ w. -/
theorem dotProduct_mulVec_unitary {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (w : n → ℂ)
    (hU : U.conjTranspose * U = 1) :
    star (U.mulVec w) ⬝ᵥ (U.mulVec w) = star w ⬝ᵥ w := by
  rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, hU, vecMul_one]

-- ========================================================================
-- Involution dot-product preservation (main lemma)
-- ========================================================================

/-- Tensoring with a self-adjoint involution A preserves dot-product norms.
    If A² = I and Aᴴ = A, then:
    star ((A ⊗ M) *ᵥ v) ⬝ᵥ ((A ⊗ M) *ᵥ v) =
    star ((I ⊗ M) *ᵥ v) ⬝ᵥ ((I ⊗ M) *ᵥ v)

    This avoids all norm/topology — purely algebraic. -/
theorem involution_tensor_dotProduct_eq (A : Involution 2)
    (M : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 × Fin 2 → ℂ) :
    star ((A.mat ⊗ₖ M).mulVec v) ⬝ᵥ ((A.mat ⊗ₖ M).mulVec v) =
    star (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ M).mulVec v) ⬝ᵥ
    (((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ M).mulVec v) := by
  -- Factor: (A ⊗ M) = (A ⊗ I) * (I ⊗ M)
  have hfactor : A.mat ⊗ₖ M =
      (A.mat ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ M) := by
    rw [← mul_kronecker_mul]; simp
  -- (A ⊗ M) *ᵥ v = (A ⊗ I) *ᵥ ((I ⊗ M) *ᵥ v)
  simp only [hfactor, ← mulVec_mulVec]
  -- Apply unitary preservation
  exact dotProduct_mulVec_unitary _ _ (involution_kronecker_one_unitary (m := 2) A)

end

end Papers.P11
