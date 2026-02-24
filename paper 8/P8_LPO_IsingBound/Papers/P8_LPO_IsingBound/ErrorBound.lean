/-
Papers/P8_LPO_IsingBound/ErrorBound.lean
The main error estimate (Theorem 4.1 from the paper).

Results:
  1. |f_N - f_∞| = (1/N)·log(1 + r^N)           (exact error)
  2. |f_N - f_∞| ≤ (1/N)·r^N                     (upper bound via log(1+x) ≤ x)
  3. |f_N - f_∞| ≤ (1/N)·exp(-N·(1-r))           (exponential decay form)

All proofs are BISH-valid. No omniscience principle used.
-/
import Papers.P8_LPO_IsingBound.FreeEnergyDecomp
import Papers.P8_LPO_IsingBound.LogBounds

namespace Papers.P8

open Real

-- ========================================================================
-- Exact error
-- ========================================================================

/-- **Exact error (Theorem 4.1, Step 1).**
    |f_N(β) - f_∞(β)| = (1/N)·log(1 + r^N). -/
lemma freeEnergy_error {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 0 < N) :
    |freeEnergyDensity β N hN - freeEnergyInfVol β| =
      (1 / (N : ℝ)) * log (1 + (eigenRatio β) ^ N) := by
  rw [freeEnergy_diff hβ hN]
  rw [abs_neg]
  exact abs_of_pos (correction_pos hβ hN)

-- ========================================================================
-- Upper bound via log(1+x) ≤ x
-- ========================================================================

/-- **Error upper bound (Theorem 4.1, Step 2).**
    |f_N(β) - f_∞(β)| ≤ (1/N)·r^N.

    This is the key estimate: the log is bounded by the linear term. -/
lemma freeEnergy_error_le_tanh_pow {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 0 < N) :
    |freeEnergyDensity β N hN - freeEnergyInfVol β| ≤
      (1 / (N : ℝ)) * (eigenRatio β) ^ N := by
  rw [freeEnergy_error hβ hN]
  apply mul_le_mul_of_nonneg_left
  · exact log_one_add_le (eigenRatio_pow_nonneg hβ N)
  · exact div_nonneg one_pos.le (Nat.cast_pos.mpr hN).le

-- ========================================================================
-- Exponential decay
-- ========================================================================

/-- **Exponential decay (Theorem 4.1, Step 3).**
    r^N ≤ exp(-N·(1-r)) where r = tanh(β).

    The decay rate is c(β) = 1 - tanh(β) = 2·exp(-β)/(exp β + exp(-β)). -/
lemma eigenRatio_pow_exp_decay {β : ℝ} (hβ : 0 < β) (N : ℕ) :
    (eigenRatio β) ^ N ≤ exp (-(↑N * (1 - eigenRatio β))) :=
  pow_le_exp_neg_mul (eigenRatio_pos hβ) (eigenRatio_lt_one β) N

/-- Combined bound: |f_N - f_∞| ≤ (1/N)·exp(-N·(1-r)). -/
lemma freeEnergy_error_exp_decay {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 0 < N) :
    |freeEnergyDensity β N hN - freeEnergyInfVol β| ≤
      (1 / (N : ℝ)) * exp (-(↑N * (1 - eigenRatio β))) := by
  calc |freeEnergyDensity β N hN - freeEnergyInfVol β|
      ≤ (1 / (N : ℝ)) * (eigenRatio β) ^ N :=
        freeEnergy_error_le_tanh_pow hβ hN
    _ ≤ (1 / (N : ℝ)) * exp (-(↑N * (1 - eigenRatio β))) := by
        apply mul_le_mul_of_nonneg_left
        · exact eigenRatio_pow_exp_decay hβ N
        · exact div_nonneg one_pos.le (Nat.cast_pos.mpr hN).le

end Papers.P8
