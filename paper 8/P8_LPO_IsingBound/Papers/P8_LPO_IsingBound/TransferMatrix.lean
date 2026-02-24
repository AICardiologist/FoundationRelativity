/-
Papers/P8_LPO_IsingBound/TransferMatrix.lean
The 2×2 transfer matrix for the 1D Ising model and its eigenvalue decomposition.

The transfer matrix is T = [[exp β, exp(-β)], [exp(-β), exp β]].
Eigenvalues: λ₊ = exp β + exp(-β) = 2·cosh β, λ₋ = exp β - exp(-β) = 2·sinh β.
Eigenvectors: v₊ = (1,1), v₋ = (1,-1).
Projectors: P₊ = ½[[1,1],[1,1]], P₋ = ½[[1,-1],[-1,1]].

The projector decomposition T = λ₊·P₊ + λ₋·P₋ is the basis for proving
Tr(T^N) = λ₊^N + λ₋^N in PartitionTrace.lean.
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Papers.P8_LPO_IsingBound.Basic

namespace Papers.P8

open Real Matrix

-- ========================================================================
-- Transfer matrix definition
-- ========================================================================

/-- The 2×2 transfer matrix for the 1D Ising model at inverse temperature β.
    T(s,s') = exp(β·s·s') where s,s' ∈ {+1,-1} encoded as Fin 2.
    Explicitly: T = [[exp β, exp(-β)], [exp(-β), exp β]]. -/
noncomputable def transferMatrix (β : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![exp β, exp (-β); exp (-β), exp β]

-- ========================================================================
-- Eigenvectors
-- ========================================================================

/-- Eigenvector for λ₊: v₊ = (1, 1). -/
def eigenVecPlus : Fin 2 → ℝ := ![1, 1]

/-- Eigenvector for λ₋: v₋ = (1, -1). -/
def eigenVecMinus : Fin 2 → ℝ := ![1, -1]

-- ========================================================================
-- Projectors (rank-1, unnormalized by factor of 2 for cleaner arithmetic)
-- ========================================================================

/-- Projector onto v₊ (scaled by 1/2): P₊ = ½·[[1,1],[1,1]]. -/
noncomputable def projPlus : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 / 2 : ℝ) • !![1, 1; 1, 1]

/-- Projector onto v₋ (scaled by 1/2): P₋ = ½·[[1,-1],[-1,1]]. -/
noncomputable def projMinus : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 / 2 : ℝ) • !![1, -1; -1, 1]

-- ========================================================================
-- Projector properties
-- ========================================================================

/-- P₊ is idempotent: P₊² = P₊. -/
lemma projPlus_sq : projPlus * projPlus = projPlus := by
  unfold projPlus
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- P₋ is idempotent: P₋² = P₋. -/
lemma projMinus_sq : projMinus * projMinus = projMinus := by
  unfold projMinus
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- P₊ · P₋ = 0. -/
lemma projPlus_mul_projMinus : projPlus * projMinus = 0 := by
  unfold projPlus projMinus
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- P₋ · P₊ = 0. -/
lemma projMinus_mul_projPlus : projMinus * projPlus = 0 := by
  unfold projPlus projMinus
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- P₊ + P₋ = I. -/
lemma projPlus_add_projMinus : projPlus + projMinus = 1 := by
  unfold projPlus projMinus
  ext i j
  fin_cases i <;> fin_cases j <;> simp

-- ========================================================================
-- Trace of projectors
-- ========================================================================

/-- Tr(P₊) = 1. -/
lemma trace_projPlus : Matrix.trace projPlus = 1 := by
  unfold projPlus Matrix.trace
  simp [diag, Fin.sum_univ_two, smul_apply]
  ring

/-- Tr(P₋) = 1. -/
lemma trace_projMinus : Matrix.trace projMinus = 1 := by
  unfold projMinus Matrix.trace
  simp [diag, Fin.sum_univ_two, smul_apply]
  ring

-- ========================================================================
-- Eigenvalue decomposition: T = λ₊ · P₊ + λ₋ · P₋
-- ========================================================================

/-- The transfer matrix decomposes as T = λ₊·P₊ + λ₋·P₋. -/
lemma transferMatrix_decomp (β : ℝ) :
    transferMatrix β =
      transferEigenPlus β • projPlus + transferEigenMinus β • projMinus := by
  unfold transferMatrix transferEigenPlus transferEigenMinus projPlus projMinus
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, cosh_eq, sinh_eq] <;>
    ring

end Papers.P8
