/-
Papers/P9_Combinatorial_Ising/CoshSinhProps.lean
Properties of the combinatorial partition function ingredients.

For β > 0:
  (a) 2·cosh(β) > 0
  (b) 2·sinh(β) > 0
  (c) 2·cosh(β) > 2·sinh(β)
  (d) 0 < tanh(β) < 1
  (e) Z_N(β) > 0

All proofs are constructively valid (BISH).
Mirrors Paper 8 EigenvalueProps.lean with combinatorial naming.
-/
import Papers.P9_Combinatorial_Ising.Basic

namespace Papers.P9

open Real

-- ========================================================================
-- Positivity
-- ========================================================================

/-- 2·cosh(β) > 0 for all β. -/
lemma twoCosh_pos (β : ℝ) : 0 < twoCosh β := by
  unfold twoCosh
  exact mul_pos two_pos (cosh_pos β)

/-- 2·sinh(β) > 0 for β > 0. -/
lemma twoSinh_pos {β : ℝ} (hβ : 0 < β) : 0 < twoSinh β := by
  unfold twoSinh
  exact mul_pos two_pos (Real.sinh_pos_iff.mpr hβ)

-- ========================================================================
-- Ordering
-- ========================================================================

/-- 2·cosh(β) > 2·sinh(β) for all β.
    Proof: sinh β < cosh β always. -/
lemma twoCosh_gt_twoSinh (β : ℝ) :
    twoSinh β < twoCosh β := by
  unfold twoCosh twoSinh
  have : sinh β < cosh β := sinh_lt_cosh β
  linarith

-- ========================================================================
-- Ratio = tanh
-- ========================================================================

/-- (2·sinh β)/(2·cosh β) = tanh(β). -/
lemma tanhRatio_eq_div (β : ℝ) :
    tanhRatio β = twoSinh β / twoCosh β := by
  unfold tanhRatio twoSinh twoCosh
  rw [tanh_eq_sinh_div_cosh]
  field_simp

/-- 0 < tanh(β) for β > 0. -/
lemma tanhRatio_pos {β : ℝ} (hβ : 0 < β) : 0 < tanhRatio β := by
  unfold tanhRatio
  rw [tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr hβ) (cosh_pos β)

/-- tanh(β) < 1 for all β. -/
lemma tanhRatio_lt_one (β : ℝ) : tanhRatio β < 1 := by
  unfold tanhRatio
  exact tanh_lt_one β

/-- 0 ≤ tanh(β) for β ≥ 0. -/
lemma tanhRatio_nonneg {β : ℝ} (hβ : 0 ≤ β) : 0 ≤ tanhRatio β := by
  unfold tanhRatio
  rw [tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr hβ) (cosh_pos β).le

-- ========================================================================
-- Partition function positivity
-- ========================================================================

/-- Z_N(β) > 0 for β > 0 and N ≥ 1. -/
lemma partitionFn_pos {β : ℝ} (hβ : 0 < β) {N : ℕ} (_hN : 0 < N) :
    0 < partitionFn β N := by
  unfold partitionFn
  exact add_pos (pow_pos (twoCosh_pos β) N)
                (pow_pos (twoSinh_pos hβ) N)

-- ========================================================================
-- Useful corollaries
-- ========================================================================

/-- 2·cosh(β) ≠ 0. -/
lemma twoCosh_ne_zero (β : ℝ) : twoCosh β ≠ 0 :=
  ne_of_gt (twoCosh_pos β)

/-- (2·cosh β)^N > 0. -/
lemma twoCosh_pow_pos (β : ℝ) (N : ℕ) :
    0 < (twoCosh β) ^ N :=
  pow_pos (twoCosh_pos β) N

/-- (2·cosh β)^N ≠ 0. -/
lemma twoCosh_pow_ne_zero (β : ℝ) (N : ℕ) :
    (twoCosh β) ^ N ≠ 0 :=
  ne_of_gt (twoCosh_pow_pos β N)

/-- (tanhRatio β) ^ N ≥ 0 for β > 0. -/
lemma tanhRatio_pow_nonneg {β : ℝ} (hβ : 0 < β) (N : ℕ) :
    0 ≤ (tanhRatio β) ^ N :=
  pow_nonneg (tanhRatio_nonneg hβ.le) N

lemma tanhRatio_pow_lt_one {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 0 < N) :
    (tanhRatio β) ^ N < 1 :=
  pow_lt_one₀ (tanhRatio_nonneg hβ.le) (tanhRatio_lt_one β) hN.ne'

/-- 1 + r^N > 0 for the ratio r = tanh β. -/
lemma one_add_tanhRatio_pow_pos {β : ℝ} (hβ : 0 < β) (N : ℕ) :
    0 < 1 + (tanhRatio β) ^ N := by
  linarith [tanhRatio_pow_nonneg hβ N]

end Papers.P9
