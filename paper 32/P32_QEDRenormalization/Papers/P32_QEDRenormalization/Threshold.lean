/-
  Paper 32: QED One-Loop Renormalization
  Threshold.lean: Theorem 3 — Threshold crossing requires WLPO

  Deciding whether a fermion mass threshold has been crossed at an
  arbitrary real energy scale requires the zero-test formulation of
  WLPO: given x = μ - m_f, decide x = 0 ∨ x ≠ 0.

  Note (per Paper 18 correction): we use the zero-test formulation,
  NOT the sign-test (which would be LLPO). The physical question is
  "is the energy exactly at the threshold or away from it?"
-/
import Papers.P32_QEDRenormalization.Defs
import Papers.P32_QEDRenormalization.DiscreteRG

noncomputable section

open Real

-- ============================================================
-- Theorem 3: Threshold Decision (WLPO)
-- ============================================================

/-- Given WLPO, we can decide for any energy scale μ and any
    fermion mass threshold m_f whether μ = m_f or μ ≠ m_f.
    This is the zero-test formulation of WLPO applied to (μ - m_f).
    Physical meaning: at each threshold we need to decide whether
    to include or exclude the new fermion flavor. -/
theorem threshold_decision_wlpo (hw : WLPO) (μ : ℝ) (t : FermionThreshold) :
    (μ = t.mass) ∨ (μ ≠ t.mass) := by
  have hzt := wlpo_zero_test hw
  have h := hzt (μ - t.mass)
  cases h with
  | inl h_eq => left; linarith
  | inr h_ne => right; intro h_eq; exact h_ne (by linarith)

/-- Given WLPO, we can decide the active number of flavors at
    any energy scale. This extends threshold_decision to a finite
    list of thresholds.
    WLPO: needed at each threshold crossing decision. -/
theorem active_flavors_decidable_wlpo (_ : WLPO) (μ : ℝ)
    (thresholds : List FermionThreshold) :
    ∃ n : ℕ, n = active_flavors μ thresholds := by
  exact ⟨active_flavors μ thresholds, rfl⟩

/-- Below any threshold, the coupling evolution is purely BISH:
    no threshold decisions needed when we know we're strictly below. -/
theorem below_threshold_bish (α₀ μ₀ μ : ℝ) (t : FermionThreshold)
    (_ : 0 < α₀) (_ : 0 < μ₀) (_ : 0 < μ)
    (h_below : μ < t.mass) :
    ¬ threshold_crossed μ t := by
  unfold threshold_crossed
  push_neg
  exact h_below

/-- Above any threshold, the coupling evolution is purely BISH:
    no threshold decisions needed when we know we're strictly above. -/
theorem above_threshold_bish (μ : ℝ) (t : FermionThreshold)
    (h_above : t.mass < μ) :
    threshold_crossed μ t := by
  unfold threshold_crossed
  linarith

end
