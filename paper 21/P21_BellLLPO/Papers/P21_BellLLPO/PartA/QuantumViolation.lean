/-
  Paper 21: Bell Nonlocality and the Constructive Cost of Disjunction: LLPO
  PartA/QuantumViolation.lean — Quantum CHSH violation (BISH)

  The quantum CHSH value S_Q = 2√2 ≈ 2.828 exceeds the classical bound of 2.
  This is a finite computation involving the singlet state and optimal
  measurement angles (Tsirelson 1980).
-/
import Papers.P21_BellLLPO.Defs.CHSH
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Papers.P21

/-- Theorem 2: The quantum CHSH value exceeds the classical bound.
    S_quantum = 2√2 > 2.
    Proof: √2 > 1 (since 2 > 1 and sqrt is monotone), so 2√2 > 2. -/
theorem S_quantum_gt_two : S_quantum > 2 := by
  unfold S_quantum
  have h1 : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

end Papers.P21
