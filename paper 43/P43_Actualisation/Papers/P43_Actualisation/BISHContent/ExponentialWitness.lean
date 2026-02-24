/-
  Paper 43: What the Ceiling Means
  BISHContent/ExponentialWitness.lean — Theorem 2: Detection time is BISH

  For all rate > 0 and eps > 0 with eps < 1, there exists a computable t0
  such that exp(-rate * t0) < eps. The witness is t0 = (log(1/eps) + 1)/rate.

  This shows that the *mathematical prediction* of radioactive decay
  is fully constructive. No omniscience principle is needed.
-/
import Papers.P43_Actualisation.Defs.Decay

namespace Papers.P43

noncomputable section

open Real

-- ========================================================================
-- Helper lemma: exp/log chain
-- ========================================================================

/-- If rate*t > log(1/eps), then exp(-(rate*t)) < eps.
    Core inequality used by the detection time theorem. -/
lemma exp_neg_mul_lt_of_gt_log_inv (rate t eps : ℝ)
    (_hr : 0 < rate) (heps : 0 < eps)
    (ht : rate * t > log (1 / eps)) :
    exp (-rate * t) < eps := by
  have : exp (-rate * t) = exp (-(rate * t)) := by ring_nf
  rw [this, exp_neg]
  rw [inv_lt_comm₀ (exp_pos _) heps]
  calc eps⁻¹ = 1 / eps := (one_div eps).symm
    _ = exp (log (1 / eps)) := (exp_log (by positivity)).symm
    _ < exp (rate * t) := exp_lt_exp_of_lt ht

-- ========================================================================
-- Theorem 2: Detection time is BISH-computable
-- ========================================================================

/-- Theorem 2 (Detection time is BISH).
    For rate > 0, eps > 0, eps < 1, the computable witness
    t0 = (log(1/eps) + 1)/rate satisfies:
    (a) 0 < t0
    (b) exp(-rate * t0) < eps

    No omniscience principle is required. The detection time
    is a closed-form BISH-computable function of the rate and tolerance. -/
theorem detection_time_bish (rate eps : ℝ)
    (hr : 0 < rate) (heps : 0 < eps) (heps1 : eps < 1) :
    let t0 := detectionTime rate eps
    0 < t0 ∧ exp (-rate * t0) < eps := by
  refine ⟨?_, ?_⟩
  · -- (a) Positivity: log(1/eps) > 0 since 1/eps > 1, plus 1 > 0
    unfold detectionTime
    apply div_pos
    · have h1eps : 1 < 1 / eps := by
        rw [one_div]
        exact one_lt_inv_iff₀.mpr ⟨heps, heps1⟩
      linarith [log_pos h1eps]
    · exact hr
  · -- (b) exp(-rate * t0) < eps via helper lemma
    show exp (-rate * detectionTime rate eps) < eps
    exact exp_neg_mul_lt_of_gt_log_inv rate (detectionTime rate eps) eps hr heps (by
      unfold detectionTime
      rw [mul_div_cancel₀ _ (ne_of_gt hr)]
      linarith)

end

end Papers.P43
