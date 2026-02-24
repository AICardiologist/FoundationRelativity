/-
Papers/P11_Entanglement/BinaryEntropy.lean
Paper 11: Constructive Cost of Quantum Entanglement — CRM over Mathlib.

Binary entropy function h(p) = −p log p − (1−p) log(1−p) using
Mathlib's negMulLog. Key result: h(1/2) = log 2.

All proofs are BISH-valid (finite arithmetic, no omniscience principles).
-/
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

namespace Papers.P11

open Real

noncomputable section

-- ========================================================================
-- Binary entropy function
-- ========================================================================

/-- Binary entropy: h(p) = η(p) + η(1 − p) where η(x) = −x log x.
    This is the von Neumann entropy of a qubit state with eigenvalues p, 1−p. -/
def binaryEntropy (p : ℝ) : ℝ :=
  negMulLog p + negMulLog (1 - p)

-- ========================================================================
-- Key values
-- ========================================================================

theorem binaryEntropy_zero : binaryEntropy 0 = 0 := by
  simp [binaryEntropy, negMulLog_zero, negMulLog_one]

theorem binaryEntropy_one : binaryEntropy 1 = 0 := by
  simp [binaryEntropy, negMulLog_zero, negMulLog_one]

/-- The binary entropy at p = 1/2 equals log 2.
    This is the maximal qubit entanglement entropy. -/
theorem binaryEntropy_half : binaryEntropy (1/2 : ℝ) = Real.log 2 := by
  unfold binaryEntropy negMulLog
  ring_nf
  rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ from by ring]
  rw [Real.log_inv]
  ring

-- ========================================================================
-- Continuity
-- ========================================================================

/-- Binary entropy is continuous on ℝ. -/
theorem continuous_binaryEntropy : Continuous binaryEntropy := by
  unfold binaryEntropy
  exact continuous_negMulLog.add (continuous_negMulLog.comp (continuous_const.sub continuous_id))

end

end Papers.P11
