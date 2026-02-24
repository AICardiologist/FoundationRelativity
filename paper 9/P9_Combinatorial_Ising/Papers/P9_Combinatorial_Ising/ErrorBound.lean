/-
Papers/P9_Combinatorial_Ising/ErrorBound.lean
The main error estimate (Theorem 4.2 from the paper).

Results:
  1. |f_N - f_∞| = (1/N)·log(1 + r^N)           (exact error)
  2. |f_N - f_∞| ≤ (1/N)·r^N                     (upper bound via log(1+x) ≤ x)
  3. |f_N - f_∞| ≤ (1/N)·exp(-N·(1-r))           (exponential decay form)

All proofs are BISH-valid. No omniscience principle used.
-/
import Papers.P9_Combinatorial_Ising.FreeEnergyDecomp
import Papers.P9_Combinatorial_Ising.LogBounds

namespace Papers.P9

open Real

-- ========================================================================
-- Exact error
-- ========================================================================

/-- **Exact error (Theorem 4.2, Step 1).**
    |f_N(β) - f_∞(β)| = (1/N)·log(1 + r^N). -/
lemma freeEnergy_error {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 0 < N) :
    |freeEnergyDensity β N hN - freeEnergyInfVol β| =
      (1 / (N : ℝ)) * log (1 + (tanhRatio β) ^ N) := by
  rw [freeEnergy_diff hβ hN]
  rw [abs_neg]
  exact abs_of_pos (correction_pos hβ hN)

-- ========================================================================
-- Upper bound via log(1+x) ≤ x
-- ========================================================================

/-- **Error upper bound (Theorem 4.2, Step 2).**
    |f_N(β) - f_∞(β)| ≤ (1/N)·r^N.

    This is the key estimate: the log is bounded by the linear term. -/
lemma freeEnergy_error_le_tanh_pow {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 0 < N) :
    |freeEnergyDensity β N hN - freeEnergyInfVol β| ≤
      (1 / (N : ℝ)) * (tanhRatio β) ^ N := by
  rw [freeEnergy_error hβ hN]
  apply mul_le_mul_of_nonneg_left
  · exact log_one_add_le (tanhRatio_pow_nonneg hβ N)
  · exact div_nonneg one_pos.le (Nat.cast_pos.mpr hN).le

-- ========================================================================
-- Exponential decay
-- ========================================================================

/-- **Exponential decay (Theorem 4.2, Step 3).**
    r^N ≤ exp(-N·(1-r)) where r = tanh(β). -/
lemma tanhRatio_pow_exp_decay {β : ℝ} (hβ : 0 < β) (N : ℕ) :
    (tanhRatio β) ^ N ≤ exp (-(↑N * (1 - tanhRatio β))) :=
  pow_le_exp_neg_mul (tanhRatio_pos hβ) (tanhRatio_lt_one β) N

/-- Combined bound: |f_N - f_∞| ≤ (1/N)·exp(-N·(1-r)). -/
lemma freeEnergy_error_exp_decay {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 0 < N) :
    |freeEnergyDensity β N hN - freeEnergyInfVol β| ≤
      (1 / (N : ℝ)) * exp (-(↑N * (1 - tanhRatio β))) := by
  calc |freeEnergyDensity β N hN - freeEnergyInfVol β|
      ≤ (1 / (N : ℝ)) * (tanhRatio β) ^ N :=
        freeEnergy_error_le_tanh_pow hβ hN
    _ ≤ (1 / (N : ℝ)) * exp (-(↑N * (1 - tanhRatio β))) := by
        apply mul_le_mul_of_nonneg_left
        · exact tanhRatio_pow_exp_decay hβ N
        · exact div_nonneg one_pos.le (Nat.cast_pos.mpr hN).le

end Papers.P9
