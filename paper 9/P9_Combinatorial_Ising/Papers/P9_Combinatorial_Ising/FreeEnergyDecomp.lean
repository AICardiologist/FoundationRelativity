/-
Papers/P9_Combinatorial_Ising/FreeEnergyDecomp.lean
Algebraic decomposition of the finite-volume free energy density.

Main result (Lemma 3.2 from the paper):
  f_N(beta) = -log(2·cosh β) - (1/N) * log(1 + r^N)

where r = tanh(beta).

This splits f_N into the infinite-volume part and a correction term,
enabling direct error estimation without passing through limits.
-/
import Papers.P9_Combinatorial_Ising.CoshSinhProps

namespace Papers.P9

open Real

-- ========================================================================
-- Partition function factorization
-- ========================================================================

/-- Z_N = (2·cosh β)^N * (1 + r^N) where r = tanhRatio β. -/
lemma partitionFn_factored {β : ℝ} (_hβ : 0 < β) (N : ℕ) :
    partitionFn β N =
      (twoCosh β) ^ N * (1 + (tanhRatio β) ^ N) := by
  unfold partitionFn
  have hpos : 0 < (twoCosh β) ^ N := twoCosh_pow_pos β N
  have hne : (twoCosh β) ^ N ≠ 0 := ne_of_gt hpos
  rw [mul_add, mul_one]
  congr 1
  rw [tanhRatio_eq_div β]
  rw [div_pow]
  rw [mul_div_cancel₀ _ hne]

-- ========================================================================
-- Free energy decomposition
-- ========================================================================

/-- **Free energy decomposition (Lemma 3.2).**
    f_N(beta) = -log(2·cosh β) - (1/N) * log(1 + r^N).

    This is the key algebraic identity that separates the infinite-volume
    contribution from the finite-size correction. -/
lemma freeEnergy_decomp {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 0 < N) :
    freeEnergyDensity β N hN =
      freeEnergyInfVol β - (1 / (N : ℝ)) * log (1 + (tanhRatio β) ^ N) := by
  unfold freeEnergyDensity freeEnergyInfVol
  rw [partitionFn_factored hβ N]
  have hpow_pos : 0 < (twoCosh β) ^ N := twoCosh_pow_pos β N
  have h1r_pos : 0 < 1 + (tanhRatio β) ^ N := one_add_tanhRatio_pow_pos hβ N
  rw [log_mul (ne_of_gt hpow_pos) (ne_of_gt h1r_pos)]
  rw [log_pow]
  have hN_ne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  field_simp
  ring

-- ========================================================================
-- Error term identity
-- ========================================================================

/-- The exact error: f_N(beta) - f_inf(beta) = -(1/N) * log(1 + r^N). -/
lemma freeEnergy_diff {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 0 < N) :
    freeEnergyDensity β N hN - freeEnergyInfVol β =
      -((1 / (N : ℝ)) * log (1 + (tanhRatio β) ^ N)) := by
  rw [freeEnergy_decomp hβ hN]
  ring

/-- The correction term is positive:
    (1/N) * log(1 + r^N) > 0 since 1 + r^N > 1 for r > 0. -/
lemma correction_pos {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 0 < N) :
    0 < (1 / (N : ℝ)) * log (1 + (tanhRatio β) ^ N) := by
  apply mul_pos
  · exact div_pos one_pos (Nat.cast_pos.mpr hN)
  · apply Real.log_pos
    have : 0 < (tanhRatio β) ^ N := pow_pos (tanhRatio_pos hβ) N
    linarith

end Papers.P9
