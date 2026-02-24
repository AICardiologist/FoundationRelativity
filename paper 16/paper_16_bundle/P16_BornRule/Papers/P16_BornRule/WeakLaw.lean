/-
Papers/P16_BornRule/WeakLaw.lean
Paper 16: The Born Rule as a Logical Artefact.

Theorem 5: Chebyshev bound for the Born rule (weak law).
  - bernoulli_variance_bound: p(1-p) ≤ 1/4
  - chebyshev_bernoulli_bound: p(1-p)/(Nε²) ≤ 1/(4Nε²)

All BISH — finite arithmetic, no limits, no choice.
-/
import Papers.P16_BornRule.Defs

namespace Papers.P16

open Finset

-- ========================================================================
-- Bernoulli variance bound: p(1-p) ≤ 1/4
-- ========================================================================

/-- The variance of a Bernoulli(p) random variable satisfies p(1-p) ≤ 1/4.
    Proof: (1/2 - p)² ≥ 0 ⟹ 1/4 - p + p² ≥ 0 ⟹ p - p² ≤ 1/4. -/
theorem bernoulli_variance_bound (p : ℝ) (_hp : 0 ≤ p) (_hp1 : p ≤ 1) :
    p * (1 - p) ≤ 1 / 4 := by
  nlinarith [sq_nonneg (1 / 2 - p)]

-- ========================================================================
-- Chebyshev bound for Bernoulli sample mean
-- ========================================================================

/-- Chebyshev bound for the Bernoulli sample mean:
    p(1-p)/(Nε²) ≤ 1/(4Nε²).
    This is the weak law — BISH, no DC, no limits. -/
theorem chebyshev_bernoulli_bound (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) :
    p * (1 - p) / (↑N * ε ^ 2) ≤ 1 / (4 * ↑N * ε ^ 2) := by
  have hN' : (0 : ℝ) < ↑N := Nat.cast_pos.mpr hN
  have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hNε : (0 : ℝ) < ↑N * ε ^ 2 := mul_pos hN' hε2
  have hvar := bernoulli_variance_bound p hp hp1
  -- p(1-p) ≤ 1/4, divide both sides by Nε²
  calc p * (1 - p) / (↑N * ε ^ 2)
      ≤ (1 / 4) / (↑N * ε ^ 2) := by
        apply div_le_div_of_nonneg_right hvar hNε.le
    _ = 1 / (4 * ↑N * ε ^ 2) := by ring

end Papers.P16
