/-
Papers/P8_LPO_IsingBound/PartitionTrace.lean
Bonus lemma: Tr(T^N) = λ₊^N + λ₋^N via projector decomposition.

This connects the direct definition of `partitionFn` (as λ₊^N + λ₋^N) to the
matrix formalism. NOT required for the main dispensability theorem — included
for completeness and physical context.

Approach:
  1. T = λ₊·P₊ + λ₋·P₋       (TransferMatrix.lean)
  2. P₊² = P₊, P₋² = P₋, P₊·P₋ = 0   (TransferMatrix.lean)
  3. T^N = λ₊^N·P₊ + λ₋^N·P₋  (induction)
  4. Tr(T^N) = λ₊^N + λ₋^N     (Tr(P₊) = Tr(P₋) = 1)
-/
import Papers.P8_LPO_IsingBound.TransferMatrix
import Papers.P8_LPO_IsingBound.EigenvalueProps

namespace Papers.P8

open Real Matrix

-- ========================================================================
-- T^N via projector decomposition (induction)
-- ========================================================================

/-- T^N = λ₊^N · P₊ + λ₋^N · P₋, by induction on N.
    Uses the orthogonal projector properties from TransferMatrix.lean. -/
lemma transferMatrix_pow (β : ℝ) (N : ℕ) :
    (transferMatrix β) ^ N =
      (transferEigenPlus β) ^ N • projPlus +
      (transferEigenMinus β) ^ N • projMinus := by
  induction N with
  | zero =>
    simp [pow_zero]
    rw [← projPlus_add_projMinus]
  | succ n ih =>
    rw [pow_succ, ih, transferMatrix_decomp β]
    -- Expand (λ₊·P₊ + λ₋·P₋) * (λ₊^n·P₊ + λ₋^n·P₋)
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
    rw [projPlus_sq, projMinus_sq,
        projPlus_mul_projMinus, projMinus_mul_projPlus]
    simp only [smul_zero, add_zero, zero_add]
    congr 1 <;> (rw [smul_smul]; ring_nf)

-- ========================================================================
-- Trace formula
-- ========================================================================

/-- **Trace formula (Lemma 2.1).**
    Tr(T^N) = λ₊^N + λ₋^N.

    This confirms that `partitionFn β N` equals the trace of the N-th power
    of the transfer matrix. -/
theorem trace_transferMatrix_pow (β : ℝ) (N : ℕ) :
    Matrix.trace ((transferMatrix β) ^ N) = partitionFn β N := by
  rw [transferMatrix_pow]
  simp only [Matrix.trace_add, Matrix.trace_smul]
  rw [trace_projPlus, trace_projMinus]
  unfold partitionFn
  simp [smul_eq_mul, mul_one]

end Papers.P8
