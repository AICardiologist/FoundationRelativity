/-
  Paper 32: QED One-Loop Renormalization
  DiscreteRG.lean: Theorem 1 — Discrete RG step is BISH

  The discrete renormalization group step is computable and
  strictly monotonic. This is pure finite arithmetic: BISH.
-/
import Papers.P32_QEDRenormalization.Defs

noncomputable section

open Real

-- ============================================================
-- Theorem 1: Discrete RG Step Growth (BISH)
-- ============================================================

/-- The QED beta coefficient is strictly positive. -/
theorem b_qed_pos : 0 < b_qed := by
  unfold b_qed
  apply div_pos (by norm_num : (0 : ℝ) < 2)
  apply mul_pos (by norm_num : (0 : ℝ) < 3) Real.pi_pos

/-- A single discrete RG step strictly increases the coupling constant.
    Physical meaning: QED coupling grows with energy (screening).
    This is pure ordered ring arithmetic: BISH. -/
theorem discrete_step_growth (α_n δ : ℝ) (hα : 0 < α_n) (hδ : 0 < δ) :
    α_n < discrete_rg_step α_n δ := by
  unfold discrete_rg_step
  linarith [mul_pos (mul_pos b_qed_pos (pow_pos hα 2)) hδ]

/-- Each iterate remains positive.
    BISH: positivity propagates through addition of positive terms. -/
theorem iterate_rg_pos (α₀ δ : ℝ) (hα : 0 < α₀) (hδ : 0 < δ) (n : ℕ) :
    0 < iterate_rg_step α₀ δ n := by
  induction n with
  | zero => exact hα
  | succ n ih =>
    unfold iterate_rg_step discrete_rg_step
    linarith [mul_pos (mul_pos b_qed_pos (pow_pos ih 2)) hδ]

/-- Helper: each step increases the iterate. -/
theorem iterate_rg_step_le_succ (α₀ δ : ℝ) (hα : 0 < α₀) (hδ : 0 < δ) (n : ℕ) :
    iterate_rg_step α₀ δ n ≤ iterate_rg_step α₀ δ (n + 1) := by
  show iterate_rg_step α₀ δ n ≤ discrete_rg_step (iterate_rg_step α₀ δ n) δ
  exact le_of_lt (discrete_step_growth _ δ (iterate_rg_pos α₀ δ hα hδ n) hδ)

/-- The discrete RG sequence is monotonically increasing
    when starting from a positive coupling with positive step size.
    BISH: just iterated application of discrete_step_growth. -/
theorem iterate_rg_monotone (α₀ δ : ℝ) (hα : 0 < α₀) (hδ : 0 < δ) :
    Monotone (iterate_rg_step α₀ δ) := by
  apply monotone_nat_of_le_succ
  exact iterate_rg_step_le_succ α₀ δ hα hδ

end
