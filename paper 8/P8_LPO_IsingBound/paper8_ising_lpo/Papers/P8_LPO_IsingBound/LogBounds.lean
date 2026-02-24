/-
Papers/P8_LPO_IsingBound/LogBounds.lean
Elementary inequalities used in the error bound.

All inequalities are constructively valid (BISH). They follow from the
fundamental bound exp(x) ≥ 1 + x (Taylor series of exp).

Key results:
  A1. log(1 + x) ≤ x           for x ≥ 0
  A2. -log(1 - δ) ≥ δ          for 0 < δ < 1
  A3. r^N ≤ exp(-N·(1-r))      for 0 < r < 1
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Papers.P8

open Real

-- ========================================================================
-- A1: log(1 + x) ≤ x for x ≥ 0
-- ========================================================================

/-- For x ≥ 0, log(1 + x) ≤ x.
    Follows from Mathlib's `log_le_sub_one_of_pos` applied with 1 + x. -/
lemma log_one_add_le {x : ℝ} (hx : 0 ≤ x) : log (1 + x) ≤ x := by
  have h1x : 0 < 1 + x := by linarith
  have := log_le_sub_one_of_pos h1x
  linarith

-- ========================================================================
-- A2: -log(1 - δ) ≥ δ for 0 < δ < 1
-- ========================================================================

/-- For 0 < δ < 1, δ ≤ -log(1 - δ).
    Equivalent to log(1-δ) ≤ -δ, which follows from 1 - δ ≤ exp(-δ). -/
lemma neg_log_one_sub_ge {δ : ℝ} (_hδ₀ : 0 < δ) (hδ₁ : δ < 1) :
    δ ≤ -log (1 - δ) := by
  have h_pos : 0 < 1 - δ := by linarith
  have h_bound := log_le_sub_one_of_pos h_pos
  -- log_le_sub_one_of_pos gives: log(1 - δ) ≤ (1 - δ) - 1 = -δ
  linarith

-- ========================================================================
-- A3: r^N ≤ exp(-N·(1-r)) for 0 < r < 1
-- ========================================================================

/-- For 0 < r < 1, r ≤ exp(-(1-r)).
    This is the base case for the geometric decay bound. -/
lemma le_exp_neg_one_sub {r : ℝ} (_hr₀ : 0 < r) (_hr₁ : r < 1) :
    r ≤ exp (-(1 - r)) := by
  -- From add_one_le_exp: -(1-r) + 1 ≤ exp(-(1-r)), i.e. r ≤ exp(-(1-r))
  have := add_one_le_exp (-(1 - r))
  linarith

/-- For 0 < r < 1 and N ≥ 1, r^N ≤ exp(-N·(1-r)).
    Exponential decay of geometric sequences. -/
lemma pow_le_exp_neg_mul {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) (N : ℕ) :
    r ^ N ≤ exp (-(↑N * (1 - r))) := by
  have hr_nn : 0 ≤ r := le_of_lt hr₀
  have h_base : r ≤ exp (-(1 - r)) := le_exp_neg_one_sub hr₀ hr₁
  have h_exp_pos : 0 < exp (-(1 - r)) := exp_pos _
  calc r ^ N ≤ (exp (-(1 - r))) ^ N :=
          pow_le_pow_left₀ hr_nn h_base N
    _ = exp (↑N * -(1 - r)) := by
          rw [← exp_nat_mul]
    _ = exp (-(↑N * (1 - r))) := by
          ring_nf

end Papers.P8
