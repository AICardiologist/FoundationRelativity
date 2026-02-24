/-
Papers/P8_LPO_IsingBound/EigenvalueProps.lean
Properties of the transfer matrix eigenvalues and eigenvalue ratio.

For β > 0:
  (a) λ₊ = 2·cosh(β) > 0
  (b) λ₋ = 2·sinh(β) > 0
  (c) λ₊ > λ₋
  (d) 0 < tanh(β) < 1
  (e) Z_N(β) > 0

All proofs are constructively valid (BISH).
-/
import Papers.P8_LPO_IsingBound.Basic

namespace Papers.P8

open Real

-- ========================================================================
-- Eigenvalue positivity
-- ========================================================================

/-- λ₊ = 2·cosh(β) > 0 for all β. -/
lemma transferEigenPlus_pos (β : ℝ) : 0 < transferEigenPlus β := by
  unfold transferEigenPlus
  exact mul_pos two_pos (cosh_pos β)

/-- λ₋ = 2·sinh(β) > 0 for β > 0. -/
lemma transferEigenMinus_pos {β : ℝ} (hβ : 0 < β) : 0 < transferEigenMinus β := by
  unfold transferEigenMinus
  exact mul_pos two_pos (Real.sinh_pos_iff.mpr hβ)

-- ========================================================================
-- Ordering
-- ========================================================================

/-- λ₊ > λ₋ for all β (in particular, for β > 0).
    Proof: sinh β < cosh β always. -/
lemma transferEigenPlus_gt_minus (β : ℝ) :
    transferEigenMinus β < transferEigenPlus β := by
  unfold transferEigenPlus transferEigenMinus
  have : sinh β < cosh β := sinh_lt_cosh β
  linarith

-- ========================================================================
-- Eigenvalue ratio = tanh
-- ========================================================================

/-- λ₋/λ₊ = tanh(β).
    Proof: (2·sinh β)/(2·cosh β) = sinh β / cosh β = tanh β. -/
lemma eigenRatio_eq_div (β : ℝ) :
    eigenRatio β = transferEigenMinus β / transferEigenPlus β := by
  unfold eigenRatio transferEigenMinus transferEigenPlus
  rw [tanh_eq_sinh_div_cosh]
  field_simp

/-- 0 < tanh(β) for β > 0.
    Proof: sinh β > 0 and cosh β > 0, so their ratio is positive. -/
lemma eigenRatio_pos {β : ℝ} (hβ : 0 < β) : 0 < eigenRatio β := by
  unfold eigenRatio
  rw [tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr hβ) (cosh_pos β)

/-- tanh(β) < 1 for all β. -/
lemma eigenRatio_lt_one (β : ℝ) : eigenRatio β < 1 := by
  unfold eigenRatio
  exact tanh_lt_one β

/-- 0 ≤ tanh(β) for β ≥ 0. -/
lemma eigenRatio_nonneg {β : ℝ} (hβ : 0 ≤ β) : 0 ≤ eigenRatio β := by
  unfold eigenRatio
  rw [tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr hβ) (cosh_pos β).le

-- ========================================================================
-- Partition function positivity
-- ========================================================================

/-- Z_N(β) > 0 for β > 0 and N ≥ 1. -/
lemma partitionFn_pos {β : ℝ} (hβ : 0 < β) {N : ℕ} (_hN : 0 < N) :
    0 < partitionFn β N := by
  unfold partitionFn
  exact add_pos (pow_pos (transferEigenPlus_pos β) N)
                (pow_pos (transferEigenMinus_pos hβ) N)

-- ========================================================================
-- Useful corollaries
-- ========================================================================

/-- λ₊ ≠ 0. -/
lemma transferEigenPlus_ne_zero (β : ℝ) : transferEigenPlus β ≠ 0 :=
  ne_of_gt (transferEigenPlus_pos β)

/-- λ₊^N > 0. -/
lemma transferEigenPlus_pow_pos (β : ℝ) (N : ℕ) :
    0 < (transferEigenPlus β) ^ N :=
  pow_pos (transferEigenPlus_pos β) N

/-- λ₊^N ≠ 0. -/
lemma transferEigenPlus_pow_ne_zero (β : ℝ) (N : ℕ) :
    (transferEigenPlus β) ^ N ≠ 0 :=
  ne_of_gt (transferEigenPlus_pow_pos β N)

/-- (eigenRatio β) ^ N ≥ 0 for β > 0. -/
lemma eigenRatio_pow_nonneg {β : ℝ} (hβ : 0 < β) (N : ℕ) :
    0 ≤ (eigenRatio β) ^ N :=
  pow_nonneg (eigenRatio_nonneg hβ.le) N

lemma eigenRatio_pow_lt_one {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 0 < N) :
    (eigenRatio β) ^ N < 1 :=
  pow_lt_one₀ (eigenRatio_nonneg hβ.le) (eigenRatio_lt_one β) hN.ne'

/-- 1 + r^N > 0 for the eigenvalue ratio r = tanh β. -/
lemma one_add_eigenRatio_pow_pos {β : ℝ} (hβ : 0 < β) (N : ℕ) :
    0 < 1 + (eigenRatio β) ^ N := by
  linarith [eigenRatio_pow_nonneg hβ N]

end Papers.P8
