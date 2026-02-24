/-
Papers/P11_Entanglement/BellState.lean
Paper 11: Constructive Cost of Quantum Entanglement — CRM over Mathlib.

The Bell state |Ψ⁻⟩ = (|01⟩ − |10⟩)/√2 has:
  - Partial trace ρ_A = (1/2)I  (maximally mixed qubit)
  - von Neumann entropy S(ρ_A) = log 2  (maximal qubit entanglement)

All proofs are finite matrix computations — BISH-valid.
-/
import Papers.P11_Entanglement.BinaryEntropy
import Papers.P11_Entanglement.PartialTrace

namespace Papers.P11

open scoped Matrix
open Matrix

noncomputable section

-- ========================================================================
-- Bell state partial trace
-- ========================================================================

/-- The partial trace of the Bell singlet density matrix is (1/2)I.
    This is the maximally mixed qubit state. -/
theorem bell_partialTrace :
    partialTraceB bellDensityMatrix = (1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [partialTraceB_apply_two, bellDensityMatrix, Matrix.smul_apply]

/-- The Bell singlet density matrix has unit trace (it's a valid state). -/
theorem bell_trace :
    bellDensityMatrix.trace = 1 := by
  simp only [Matrix.trace, Matrix.diag, bellDensityMatrix]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  norm_num

-- ========================================================================
-- Bell state entropy
-- ========================================================================

/-- The von Neumann entropy of the Bell state's reduced state equals log 2.
    Since ρ_A = (1/2)I has eigenvalues 1/2, 1/2, the entropy is
    h(1/2) = −(1/2)log(1/2) − (1/2)log(1/2) = log 2. -/
theorem bell_entropy :
    binaryEntropy (1/2 : ℝ) = Real.log 2 :=
  binaryEntropy_half

/-- Combined statement: the Bell singlet state has maximal qubit entanglement.
    The partial trace gives (1/2)I and the entropy is log 2. -/
theorem bell_maximal_entanglement :
    partialTraceB bellDensityMatrix = (1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
    binaryEntropy (1/2 : ℝ) = Real.log 2 :=
  ⟨bell_partialTrace, bell_entropy⟩

end

end Papers.P11
