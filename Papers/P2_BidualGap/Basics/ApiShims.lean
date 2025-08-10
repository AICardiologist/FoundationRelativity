/-
Papers/P2_BidualGap/Basics/ApiShims.lean

Purpose: Battle‑tested API shims extracted from the axiom‑clean implementation.
Status: Compiles cleanly; patterns are resilient to mathlib drift.
-/
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Real.Basic

namespace Papers.P2.Basics.ApiShims

/-! ## Unit-sphere normalization -/

/-- For nonzero `x`, `‖(‖x‖)⁻¹ • x‖ = 1`.  Robust simp‑driven proof. -/
lemma unitSphere_normalize_norm
  {E} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {x : E} (hx : x ≠ 0) :
  ‖(‖x‖)⁻¹ • x‖ = 1 := by
  have hxpos : 0 < ‖x‖ := by simpa [norm_pos_iff] using hx
  have h1 : ‖(‖x‖)⁻¹ • x‖ = ‖(‖x‖)⁻¹‖ * ‖x‖ := by
    simpa using norm_smul ((‖x‖)⁻¹) x
  have h2 : ‖(‖x‖)⁻¹‖ = (‖x‖)⁻¹ := by
    simp [Real.norm_of_nonneg (le_of_lt (inv_pos.mpr hxpos))]
  have hxne : (‖x‖ : ℝ) ≠ 0 := ne_of_gt hxpos
  have : ‖(‖x‖)⁻¹ • x‖ = (‖x‖)⁻¹ * ‖x‖ := by simpa [h2] using h1
  -- let `simp` eliminate the inverse using `hxne`
  simpa [hxne] using this

/-- Scaling the normalized vector back by `‖x‖` returns `x`. -/
lemma unitSphere_scale_back
  {E} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {x : E} (hx : x ≠ 0) :
  (‖x‖ : ℝ) • ((‖x‖)⁻¹ • x) = x := by
  have hxpos : 0 < ‖x‖ := by simpa [norm_pos_iff] using hx
  have hxne : (‖x‖ : ℝ) ≠ 0 := ne_of_gt hxpos
  -- (‖x‖) • ((‖x‖)⁻¹ • x) = ((‖x‖) * (‖x‖)⁻¹) • x = 1 • x = x
  simp [smul_smul, hxne, one_smul]

/-! ## Operator‑norm inequalities -/

/-- If `∀ x, ‖T x‖ ≤ (‖T‖/2) * ‖x‖`, then `‖T‖ ≤ ‖T‖/2`. -/
lemma opNorm_pointwise_half_le
  {E} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (T : E →L[ℝ] ℝ)
  (h : ∀ x, ‖T x‖ ≤ (‖T‖ / 2) * ‖x‖) :
  ‖T‖ ≤ ‖T‖ / 2 := by
  have hnonneg : 0 ≤ ‖T‖ / 2 := by exact div_nonneg (norm_nonneg _) (by norm_num)
  simpa using
    ContinuousLinearMap.opNorm_le_bound T hnonneg (by intro x; simpa [mul_comm] using h x)

/-- If `∀ x, ‖T x‖ ≤ (‖T‖/2) * ‖x‖`, then `T = 0`.  
    (Pure norm‑algebra: no approximate‑supremum machinery needed.) -/
lemma opNorm_half_bound_implies_zero
  {E} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (T : E →L[ℝ] ℝ)
  (h : ∀ x, ‖T x‖ ≤ (‖T‖ / 2) * ‖x‖) :
  T = 0 := by
  have h' : ‖T‖ ≤ ‖T‖ / 2 := opNorm_pointwise_half_le T h
  -- multiply both sides by 2 ≥ 0
  have h'2 := (mul_le_mul_of_nonneg_left h' (show 0 ≤ (2:ℝ) by norm_num))
  -- 2*‖T‖ ≤ 2*(‖T‖/2) = ‖T‖
  have h2T_le_T : 2 * ‖T‖ ≤ ‖T‖ := by
    simpa [two_mul, add_halves] using h'2
  -- hence ‖T‖ ≤ 0
  have hle0 : ‖T‖ ≤ 0 := by
    have := sub_nonpos.mpr h2T_le_T
    -- 2*‖T‖ - ‖T‖ = ‖T‖
    simpa [two_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  have hzero : ‖T‖ = 0 := le_antisymm hle0 (norm_nonneg _)
  exact (norm_eq_zero.mp hzero)

/-! ## Stable aliases (name‑drift guards) -/

/-- Stable wrapper for `T.le_opNorm`. -/
lemma le_opNorm' {E} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (T : E →L[ℝ] ℝ) (x : E) : ‖T x‖ ≤ ‖T‖ * ‖x‖ := T.le_opNorm x

/-- On reals, `|·| = ‖·‖`. -/
@[simp] lemma abs_eq_norm_real (t : ℝ) : |t| = ‖t‖ := rfl

/-- Norm of a real product. -/
lemma norm_mul_real (s t : ℝ) : ‖s * t‖ = ‖s‖ * ‖t‖ := norm_mul s t

end Papers.P2.Basics.ApiShims