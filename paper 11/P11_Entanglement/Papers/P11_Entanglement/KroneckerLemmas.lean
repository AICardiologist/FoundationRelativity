/-
Papers/P11_Entanglement/KroneckerLemmas.lean
Paper 11: Constructive Cost of Quantum Entanglement — CRM over Mathlib.

Bridge lemmas for Kronecker products not in Mathlib:
negation, subtraction, and involution properties.

All proofs are algebraic — BISH-valid.
-/
import Papers.P11_Entanglement.Defs

namespace Papers.P11

open scoped Matrix Kronecker
open Matrix

-- ========================================================================
-- Negation and subtraction for Kronecker products
-- ========================================================================

theorem neg_kronecker {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Matrix (Fin m) (Fin m) ℂ) :
    (-A) ⊗ₖ B = -(A ⊗ₖ B) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [kroneckerMap_apply, neg_mul]

theorem kronecker_neg {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Matrix (Fin m) (Fin m) ℂ) :
    A ⊗ₖ (-B) = -(A ⊗ₖ B) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [kroneckerMap_apply, mul_neg]

theorem sub_kronecker {n m : ℕ} (A₁ A₂ : Matrix (Fin n) (Fin n) ℂ)
    (B : Matrix (Fin m) (Fin m) ℂ) :
    (A₁ - A₂) ⊗ₖ B = A₁ ⊗ₖ B - A₂ ⊗ₖ B := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [kroneckerMap_apply, sub_mul]

theorem kronecker_sub {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (B₁ B₂ : Matrix (Fin m) (Fin m) ℂ) :
    A ⊗ₖ (B₁ - B₂) = A ⊗ₖ B₁ - A ⊗ₖ B₂ := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [kroneckerMap_apply, mul_sub]

-- ========================================================================
-- CHSH decomposition
-- ========================================================================

/-- The CHSH operator decomposes as C = A ⊗ (B+B') + A' ⊗ (B−B').
    This is the key algebraic factorization for the Tsirelson bound proof. -/
theorem chsh_decomp (A A' B B' : Involution 2) :
    chshOperator A A' B B' =
    A.mat ⊗ₖ (B.mat + B'.mat) + A'.mat ⊗ₖ (B.mat - B'.mat) := by
  unfold chshOperator
  rw [kronecker_add, kronecker_sub]
  abel

-- ========================================================================
-- Kronecker product of involutions
-- ========================================================================

/-- The square of a Kronecker product: (A ⊗ B)² = A² ⊗ B². -/
theorem kronecker_sq {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Matrix (Fin m) (Fin m) ℂ) :
    (A ⊗ₖ B) * (A ⊗ₖ B) = (A * A) ⊗ₖ (B * B) :=
  (mul_kronecker_mul A A B B).symm

/-- A Kronecker product of involutions is an involution. -/
theorem kronecker_involution_sq {n m : ℕ} (A : Involution n) (B : Involution m) :
    (A.mat ⊗ₖ B.mat) * (A.mat ⊗ₖ B.mat) = 1 := by
  rw [kronecker_sq, A.sq_eq_one, B.sq_eq_one, one_kronecker_one]

-- ========================================================================
-- Sum-of-squares identity for Bob's observables
-- ========================================================================

/-- For involutions B, B': (B+B')² + (B−B')² = 4I.
    This is the algebraic heart of the Tsirelson bound. -/
theorem sum_sq_bob (B B' : Involution 2) :
    (B.mat + B'.mat) * (B.mat + B'.mat) +
    (B.mat - B'.mat) * (B.mat - B'.mat) =
    4 • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hB := B.sq_eq_one
  have hB' := B'.sq_eq_one
  -- Expand using non-commutative distributivity
  have expand_plus : (B.mat + B'.mat) * (B.mat + B'.mat) =
      B.mat * B.mat + B.mat * B'.mat + B'.mat * B.mat + B'.mat * B'.mat := by
    simp [mul_add, add_mul]; abel
  have expand_minus : (B.mat - B'.mat) * (B.mat - B'.mat) =
      B.mat * B.mat - B.mat * B'.mat - B'.mat * B.mat + B'.mat * B'.mat := by
    simp [mul_sub, sub_mul]; abel
  rw [expand_plus, expand_minus]
  -- Cross terms cancel, leaving 2B² + 2B'²
  have : B.mat * B.mat + B.mat * B'.mat + B'.mat * B.mat + B'.mat * B'.mat +
         (B.mat * B.mat - B.mat * B'.mat - B'.mat * B.mat + B'.mat * B'.mat) =
         2 • (B.mat * B.mat) + 2 • (B'.mat * B'.mat) := by abel
  rw [this, hB, hB']
  norm_num

-- ========================================================================
-- Conjugate transpose of Kronecker products (Hermitian involution)
-- ========================================================================

/-- For Hermitian involutions, (A ⊗ I)ᴴ * (A ⊗ I) = I.
    Proof: Aᴴ = A (Hermitian) and A*A = I (involution), so
    (A⊗I)ᴴ * (A⊗I) = (Aᴴ⊗Iᴴ) * (A⊗I) = (A*A)⊗(I*I) = I⊗I = I. -/
theorem involution_kronecker_one_unitary {n m : ℕ} (A : Involution n) :
    (A.mat ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)).conjTranspose *
    (A.mat ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) = 1 := by
  rw [conjTranspose_kronecker, conjTranspose_one]
  rw [← mul_kronecker_mul]
  have : A.mat.conjTranspose * A.mat = 1 := by
    rw [A.hermitian]; exact A.sq_eq_one
  rw [this, mul_one, one_kronecker_one]

end Papers.P11
