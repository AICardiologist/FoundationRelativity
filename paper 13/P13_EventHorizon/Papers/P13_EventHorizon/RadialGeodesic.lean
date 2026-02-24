/-
Papers/P13_EventHorizon/RadialGeodesic.lean
Module 2: Radial geodesic equation and cycloid parametrization.

For a particle dropped from rest at the horizon (E = 1), the radial timelike
geodesic in the Schwarzschild interior has the closed-form cycloid solution:
  r(η) = M(1 + cos η)       η ∈ [0, π]
  τ(η) = M(η + sin η)       τ ∈ [0, πM]

This avoids formalizing ODE existence/uniqueness theory. All properties
(monotonicity, boundedness, endpoint values) follow from explicit trigonometry.
-/
import Papers.P13_EventHorizon.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue

namespace Papers.P13

open Real Set

-- ========================================================================
-- Helper: cos η < 1 for η ∈ (0, π)
-- ========================================================================

/-- cos η < 1 for η ≠ 0 with |η| < 2π. Uses cos_eq_one_iff_of_lt_of_lt. -/
theorem cos_lt_one_of_ne_zero_of_abs_lt {η : ℝ} (hne : η ≠ 0)
    (h1 : -(2 * π) < η) (h2 : η < 2 * π) : cos η < 1 := by
  have hle := cos_le_one η
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exfalso; apply hne
    exact (cos_eq_one_iff_of_lt_of_lt h1 h2).mp h

/-- cos η < 1 for η ∈ (0, π). -/
theorem cos_lt_one_of_mem_Ioo {η : ℝ} (hη : η ∈ Ioo 0 π) : cos η < 1 := by
  have h1 : 0 < η := hη.1
  have h2 : η < π := hη.2
  exact cos_lt_one_of_ne_zero_of_abs_lt (ne_of_gt h1)
    (by linarith [pi_pos]) (by linarith [pi_pos])

/-- cos η > -1 for η ∈ (0, π). If cos η = -1, then by cos_eq_neg_one_iff
    η = π + k(2π) for some integer k. For η ∈ (0, π), this is impossible. -/
theorem neg_one_lt_cos_of_mem_Ioo {η : ℝ} (hη : η ∈ Ioo 0 π) : -1 < cos η := by
  rcases lt_or_eq_of_le (neg_one_le_cos η) with h | h
  · exact h
  · exfalso
    have h' : cos η = -1 := h.symm
    rw [cos_eq_neg_one_iff] at h'
    obtain ⟨k, hk⟩ := h'
    -- η = π + k * (2π), and η ∈ (0, π)
    -- From hk: π + k * (2π) = η, so k * (2π) = η - π
    have hk_eq : (k : ℝ) * (2 * π) = η - π := by linarith
    -- Since 0 < η < π, we get -π < η - π < 0
    have hhi : (k : ℝ) * (2 * π) < 0 := by linarith [hη.1, hη.2]
    -- k * (2π) < 0 implies k < 0 (since 2π > 0)
    have hk_neg : k < 0 := by
      by_contra h_nn
      push_neg at h_nn
      have : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h_nn
      have : (k : ℝ) * (2 * π) ≥ 0 := mul_nonneg this (by linarith [pi_pos])
      linarith
    -- k < 0 means k ≤ -1 (integers), so k * (2π) ≤ -2π
    have hk_le : k ≤ -1 := by omega
    have : (k : ℝ) ≤ -1 := by exact_mod_cast hk_le
    have : (k : ℝ) * (2 * π) ≤ -1 * (2 * π) :=
      mul_le_mul_of_nonneg_right this (by linarith [pi_pos])
    -- But -2π < -π, contradicting η - π > -π
    linarith [hη.1, pi_pos]

-- ========================================================================
-- Cycloid parametrization of the radial geodesic
-- ========================================================================

/-- Radial coordinate along the cycloid geodesic: r(η) = M(1 + cos η).
    At η = 0: r = 2M (the horizon). At η = π: r = 0 (the singularity). -/
noncomputable def r_cycloid (M η : ℝ) : ℝ := M * (1 + cos η)

/-- Proper time along the cycloid geodesic: τ(η) = M(η + sin η).
    At η = 0: τ = 0 (entry). At η = π: τ = πM (finite proper time to singularity). -/
noncomputable def τ_cycloid (M η : ℝ) : ℝ := M * (η + sin η)

-- ========================================================================
-- Endpoint values
-- ========================================================================

/-- At η = 0, the geodesic starts at the horizon r = 2M. -/
theorem r_cycloid_at_zero (M : ℝ) : r_cycloid M 0 = 2 * M := by
  simp [r_cycloid, cos_zero]
  ring

/-- At η = π, the geodesic reaches the singularity r = 0. -/
theorem r_cycloid_at_pi (M : ℝ) : r_cycloid M π = 0 := by
  simp [r_cycloid, cos_pi]

/-- At η = 0, proper time is zero. -/
theorem τ_cycloid_at_zero (M : ℝ) : τ_cycloid M 0 = 0 := by
  simp [τ_cycloid, sin_zero]

/-- At η = π, proper time is finite: τ = πM. -/
theorem τ_cycloid_at_pi (M : ℝ) : τ_cycloid M π = M * π := by
  simp [τ_cycloid, sin_pi]

/-- The proper time to the singularity is positive for M > 0. -/
theorem τ_star_pos (M : ℝ) (hM : M > 0) : τ_cycloid M π > 0 := by
  rw [τ_cycloid_at_pi]
  exact mul_pos hM pi_pos

-- ========================================================================
-- Interior membership
-- ========================================================================

/-- For η ∈ (0, π) and M > 0, the geodesic lies in the interior: 0 < r(η) < 2M. -/
theorem r_cycloid_interior {M η : ℝ} (hM : M > 0) (hη : η ∈ Ioo 0 π) :
    Interior M (r_cycloid M η) where
  mass_pos := hM
  r_pos := by
    unfold r_cycloid
    apply mul_pos hM
    have : -1 < cos η := neg_one_lt_cos_of_mem_Ioo hη
    linarith
  r_inside := by
    unfold r_cycloid
    have hcos : cos η < 1 := cos_lt_one_of_mem_Ioo hη
    nlinarith

-- ========================================================================
-- Non-negativity
-- ========================================================================

/-- r(η) ≥ 0 for η ∈ [0, π] and M > 0. -/
theorem r_cycloid_nonneg {M η : ℝ} (hM : M > 0) (_hη : η ∈ Icc 0 π) :
    0 ≤ r_cycloid M η := by
  unfold r_cycloid
  apply mul_nonneg (le_of_lt hM)
  linarith [neg_one_le_cos η]

-- ========================================================================
-- Monotonicity of r_cycloid (decreasing in η)
-- ========================================================================

/-- The derivative of r_cycloid with respect to η is -M sin η. -/
theorem hasDerivAt_r_cycloid (M η : ℝ) :
    HasDerivAt (r_cycloid M ·) (-M * sin η) η := by
  unfold r_cycloid
  have := (hasDerivAt_cos η).const_add 1 |>.const_mul M
  simp only [mul_neg] at this
  convert this using 1
  ring

/-- sin η > 0 for η ∈ (0, π). -/
theorem sin_pos_of_mem_Ioo {η : ℝ} (hη : η ∈ Ioo 0 π) : sin η > 0 :=
  sin_pos_of_pos_of_lt_pi hη.1 hη.2

/-- r_cycloid M is continuous. -/
theorem continuous_r_cycloid (M : ℝ) : Continuous (r_cycloid M ·) := by
  unfold r_cycloid
  exact continuous_const.mul (continuous_const.add continuous_cos)

/-- r_cycloid is strictly decreasing on [0, π] for M > 0. -/
theorem r_cycloid_strictAntiOn (M : ℝ) (hM : M > 0) :
    StrictAntiOn (r_cycloid M ·) (Icc 0 π) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 π) (continuous_r_cycloid M).continuousOn
  intro η hη
  rw [interior_Icc] at hη
  rw [(hasDerivAt_r_cycloid M η).deriv]
  have hsin := sin_pos_of_mem_Ioo hη
  nlinarith

-- ========================================================================
-- Monotonicity of τ_cycloid (increasing in η)
-- ========================================================================

/-- The derivative of τ_cycloid with respect to η is M(1 + cos η). -/
theorem hasDerivAt_τ_cycloid (M η : ℝ) :
    HasDerivAt (τ_cycloid M ·) (M * (1 + cos η)) η := by
  unfold τ_cycloid
  have := ((hasDerivAt_id η).add (hasDerivAt_sin η)).const_mul M
  simp only [mul_add, mul_one] at this
  convert this using 1
  ring

/-- τ_cycloid M is continuous. -/
theorem continuous_τ_cycloid (M : ℝ) : Continuous (τ_cycloid M ·) := by
  unfold τ_cycloid
  exact continuous_const.mul (continuous_id.add continuous_sin)

/-- τ_cycloid is strictly increasing on [0, π] for M > 0. -/
theorem τ_cycloid_strictMonoOn (M : ℝ) (hM : M > 0) :
    StrictMonoOn (τ_cycloid M ·) (Icc 0 π) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 π) (continuous_τ_cycloid M).continuousOn
  intro η hη
  rw [interior_Icc] at hη
  rw [(hasDerivAt_τ_cycloid M η).deriv]
  apply mul_pos hM
  have : -1 < cos η := neg_one_lt_cos_of_mem_Ioo hη
  linarith

-- ========================================================================
-- The radial geodesic ODE (for reference / BISH content)
-- ========================================================================

/-- The right-hand side of the radial geodesic equation:
    (dr/dτ)² = E² - (1 - 2M/r) = E² - f(M,r).
    In the interior, f < 0, so this is E² + |f| > 0: the particle must move in r. -/
noncomputable def radial_geodesic_rhs (M E r : ℝ) : ℝ := E ^ 2 - f M r

/-- In the interior with E ≥ 1, the geodesic velocity squared is strictly positive.
    This means the particle necessarily moves inward (dr/dτ ≠ 0). -/
theorem radial_velocity_positive_interior {M r : ℝ} (h_int : Interior M r)
    {E : ℝ} (_hE : E ≥ 1) : radial_geodesic_rhs M E r > 0 := by
  unfold radial_geodesic_rhs
  have hf := f_neg_interior h_int
  nlinarith [sq_nonneg E, sq_nonneg (1 : ℝ)]

-- ========================================================================
-- Key approaching-singularity lemma (constructive / BISH)
-- ========================================================================

/-- For any ε > 0, there exists η ∈ (0, π) such that r(η) < ε.
    This is the BISH content: we can get arbitrarily close to r = 0
    without asserting that r actually reaches 0. -/
theorem r_cycloid_approaching {M : ℝ} (hM : M > 0) {ε : ℝ} (hε : ε > 0) :
    ∃ η ∈ Ioo 0 π, r_cycloid M η < ε := by
  -- r_cycloid M is continuous and r_cycloid M π = 0 < ε.
  -- By continuity at π, ∃ δ > 0 with |r_cycloid M η - 0| < ε for |η - π| < δ.
  have hcont := continuous_r_cycloid M
  have h_at_pi : r_cycloid M π = 0 := r_cycloid_at_pi M
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuousAt_iff.mp hcont.continuousAt ε hε
  -- Pick η₀ = π - min(δ/2, π/2), which is in (0, π) and within δ of π.
  set η₀ := π - min (δ / 2) (π / 2) with hη₀_def
  have hmin_pos : 0 < min (δ / 2) (π / 2) := lt_min (half_pos hδ_pos) (half_pos pi_pos)
  have hη₀_lt_pi : η₀ < π := by linarith
  have hη₀_pos : 0 < η₀ := by
    have : min (δ / 2) (π / 2) ≤ π / 2 := min_le_right _ _
    linarith [pi_pos]
  have hη₀_mem : η₀ ∈ Ioo 0 π := ⟨hη₀_pos, hη₀_lt_pi⟩
  refine ⟨η₀, hη₀_mem, ?_⟩
  have hdist : dist η₀ π < δ := by
    rw [Real.dist_eq]
    have : η₀ - π = -(min (δ / 2) (π / 2)) := by rw [hη₀_def]; ring
    rw [this, abs_neg, abs_of_pos hmin_pos]
    exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ_pos)
  have hball := hδ hdist
  rw [h_at_pi] at hball
  simp only [dist_zero_right] at hball
  rwa [Real.norm_of_nonneg (r_cycloid_nonneg hM ⟨le_of_lt hη₀_pos, le_of_lt hη₀_lt_pi⟩)] at hball

end Papers.P13
