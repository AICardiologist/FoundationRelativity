/-
Papers/P11_Entanglement/Defs.lean
Paper 11: Constructive Cost of Quantum Entanglement — CRM over Mathlib.

Core definitions: Involution structure, CHSH operator, Pauli matrices,
partial trace, Bell state density matrix.

All definitions use Mathlib's Matrix and Kronecker product APIs.
-/
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian

namespace Papers.P11

open scoped Matrix Kronecker
open Matrix

noncomputable section

-- ========================================================================
-- Involution: self-adjoint unitary with A² = I
-- ========================================================================

/-- A self-adjoint involution on ℂⁿ: a Hermitian matrix with A² = I.
    These are the ±1-valued observables of quantum mechanics. -/
structure Involution (n : ℕ) where
  mat : Matrix (Fin n) (Fin n) ℂ
  sq_eq_one : mat * mat = 1
  hermitian : mat.conjTranspose = mat

-- ========================================================================
-- CHSH operator
-- ========================================================================

/-- The CHSH operator on ℂ² ⊗ ℂ², defined as:
    C = A ⊗ B + A ⊗ B' + A' ⊗ B − A' ⊗ B'
    where A, A' are Alice's observables and B, B' are Bob's. -/
def chshOperator (A A' B B' : Involution 2) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  A.mat ⊗ₖ B.mat + A.mat ⊗ₖ B'.mat + A'.mat ⊗ₖ B.mat - A'.mat ⊗ₖ B'.mat

-- ========================================================================
-- Pauli matrices
-- ========================================================================

/-- Pauli Z matrix: diag(1, -1). -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -1]

/-- Pauli X matrix: off-diagonal ones. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

-- ========================================================================
-- Partial trace (trace out subsystem B)
-- ========================================================================

/-- Partial trace over the second subsystem (Bob) of a bipartite density matrix.
    For ρ on ℂ^n ⊗ ℂ^m, returns the reduced state on ℂ^n. -/
def partialTraceB {n m : ℕ} (ρ : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => ∑ k : Fin m, ρ (i, k) (j, k)

-- ========================================================================
-- Bell state density matrix
-- ========================================================================

/-- The singlet Bell state density matrix |Ψ⁻⟩⟨Ψ⁻| where
    |Ψ⁻⟩ = (|01⟩ − |10⟩)/√2.
    As a matrix on ℂ² ⊗ ℂ²:
      ρ = (1/2)(|01⟩⟨01| − |01⟩⟨10| − |10⟩⟨01| + |10⟩⟨10|) -/
def bellDensityMatrix : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun i j =>
    if i = (0, 1) ∧ j = (0, 1) then 1/2
    else if i = (0, 1) ∧ j = (1, 0) then -1/2
    else if i = (1, 0) ∧ j = (0, 1) then -1/2
    else if i = (1, 0) ∧ j = (1, 0) then 1/2
    else 0

end

end Papers.P11
