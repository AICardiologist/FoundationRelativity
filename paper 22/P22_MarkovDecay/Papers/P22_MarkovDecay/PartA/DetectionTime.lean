/-
  Paper 22: Markov's Principle and the Constructive Cost of Eventual Decay
  PartA/DetectionTime.lean — Detection time works for known bounds

  For any λ ≥ q > 0 and ε ∈ (0,1):
    T = ln(1/ε)/q > 0  and  P(T, λ) = exp(-λT) ≤ ε

  This is BISH: the explicit lower bound q makes everything computable.
-/
import Papers.P22_MarkovDecay.Defs.Decay
import Papers.P22_MarkovDecay.Defs.EncodedRate

namespace Papers.P22

noncomputable section

-- ========================================================================
-- Helper: exp(-log(1/ε)) = ε
-- ========================================================================

/-- For ε > 0: exp(-log(1/ε)) = ε. -/
private theorem exp_neg_log_inv (eps : ℝ) (heps : 0 < eps) :
    Real.exp (-Real.log (1 / eps)) = eps := by
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (ne_of_gt heps)]
  rw [Real.log_one]
  simp only [zero_sub]
  rw [neg_neg]
  exact Real.exp_log heps

-- ========================================================================
-- Detection time is positive
-- ========================================================================

/-- The detection time T = ln(1/ε)/q is positive for q > 0, ε ∈ (0,1). -/
theorem detectionTime_pos (q eps : ℝ)
    (hq : 0 < q) (heps : 0 < eps) (heps1 : eps < 1) :
    0 < detectionTime eps q := by
  unfold detectionTime
  apply div_pos
  · apply Real.log_pos
    rw [lt_div_iff₀ heps]
    linarith
  · exact hq

-- ========================================================================
-- Detection time works
-- ========================================================================

/-- For λ ≥ q > 0 and ε ∈ (0,1):
    P(T, λ) = exp(-λ · T) ≤ ε where T = ln(1/ε)/q. -/
theorem detection_time_works (lambda_ q eps : ℝ)
    (hq : 0 < q) (hlq : q ≤ lambda_) (heps : 0 < eps) (heps1 : eps < 1) :
    survivalProb lambda_ (detectionTime eps q) ≤ eps := by
  unfold survivalProb detectionTime
  -- Goal: exp(-(λ · (log(1/ε)/q))) ≤ ε
  -- Step 1: since λ ≥ q > 0 and log(1/ε) > 0:
  --   -(λ · (log(1/ε)/q)) ≤ -(q · (log(1/ε)/q)) = -log(1/ε)
  have hlog_pos : 0 < Real.log (1 / eps) := by
    apply Real.log_pos; rw [lt_div_iff₀ heps]; linarith
  have hT_pos : 0 < Real.log (1 / eps) / q := div_pos hlog_pos hq
  have h_neg_le : -(lambda_ * (Real.log (1 / eps) / q)) ≤
      -(q * (Real.log (1 / eps) / q)) := by
    apply neg_le_neg
    apply mul_le_mul_of_nonneg_right hlq (le_of_lt hT_pos)
  -- Step 2: simplify q · (log(1/ε)/q) = log(1/ε)
  have h_simpl : q * (Real.log (1 / eps) / q) = Real.log (1 / eps) := by
    field_simp
  rw [h_simpl] at h_neg_le
  -- Step 3: exp is monotone
  calc Real.exp (-(lambda_ * (Real.log (1 / eps) / q)))
      ≤ Real.exp (-(Real.log (1 / eps))) := by
        exact Real.exp_le_exp.mpr h_neg_le
    _ = eps := exp_neg_log_inv eps heps

-- ========================================================================
-- Detection with witness (explicit bound from α(k) = true)
-- ========================================================================

/-- When α(k) = true, the encoded rate has an explicit lower bound
    (1/2)^(k+1), and the detection time is computable. -/
theorem detection_with_witness (α : ℕ → Bool) (k : ℕ)
    (hk : α k = true) (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1) :
    ∃ (T : ℝ), 0 < T ∧ survivalProb (encodedRate α) T ≤ eps := by
  -- Lower bound q = (1/2)^(k+1) > 0
  set q := ((1 : ℝ) / 2) ^ (k + 1) with hq_def
  have hq_pos : 0 < q := pow_pos (by norm_num) _
  -- encodedRate α ≥ q (from the witness)
  have hlq : q ≤ encodedRate α := by
    unfold encodedRate
    have hterm : encodedRateTerm α k = q := by
      unfold encodedRateTerm; rw [if_pos hk]
    rw [← hterm]
    exact (encodedRate_summable α).le_tsum k (fun n _hn => encodedRateTerm_nonneg α n)
  exact ⟨detectionTime eps q,
    detectionTime_pos q eps hq_pos heps heps1,
    detection_time_works (encodedRate α) q eps hq_pos hlq heps heps1⟩

end

end Papers.P22
