/-
Papers/P19_WKBTunneling/Calibration/PartB.lean
Theorem 4: The Turning Point Problem (TPP) is equivalent to LLPO.

This is the core new result of Paper 19. The proof factors through the
known equivalence ExactIVT ↔ LLPO (axiomatized, citing Bridges-Richman 1987).

  TPP ↔ ExactIVT ↔ LLPO

Forward (TPP → ExactIVT): Given a sign-changing continuous f on [a,b],
  construct a Barrier from f and extract the root from a turning point.

Backward (ExactIVT → TPP): Given a Barrier, apply ExactIVT twice
  (rescaled to appropriate subintervals) to find the two turning points.

Axiom audit expectation: [propext, Classical.choice, Quot.sound, exact_ivt_iff_llpo]
  - Classical.choice from Mathlib (Continuous, neg, sub)
  - exact_ivt_iff_llpo is the single custom axiom (LLPO-level cost)
  - NO bmc_iff_lpo (that's Part C only)
-/
import Papers.P19_WKBTunneling.Barrier.General

noncomputable section
namespace Papers.P19

-- ========================================================================
-- Backward direction: ExactIVT → TPP
-- ========================================================================

/-- ExactIVT implies the Turning Point Problem is solvable.
    Given a Barrier B (with V(0) < E, V(c) > E for some c, V(1) < E),
    we find turning points by applying the rescaled IVT twice:
    once on [0, c] and once on [c, 1]. -/
theorem tpp_of_ivt (hIVT : ExactIVT) : TPP := by
  intro B
  -- Extract the peak point c
  obtain ⟨c, hc0, hc1, hVc⟩ := B.h_peak
  -- Define f(x) = V(x) - E. Then f(0) < 0, f(c) > 0, f(1) < 0.
  set f : ℝ → ℝ := fun x => B.V x - B.E with hf_def
  have hf_cont : Continuous f := B.hV_cont.sub continuous_const
  have hf0 : f 0 < 0 := by simp [hf_def]; linarith [B.h_left]
  have hfc : f c > 0 := by simp [hf_def]; linarith
  have hf1 : f 1 < 0 := by simp [hf_def]; linarith [B.h_right]
  -- Case: c = 0 is impossible (f(0) < 0 and f(c) > 0)
  by_cases hc0' : c = 0
  · exfalso; rw [hc0'] at hfc; linarith
  by_cases hc1' : c = 1
  · exfalso; rw [hc1'] at hfc; linarith
  have hc0_lt : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hc0')
  have hc1_lt : c < 1 := lt_of_le_of_ne hc1 hc1'
  -- Apply IVT on [0, c]: f(0) < 0 < f(c), get x₁ with f(x₁) = 0
  obtain ⟨x₁, hx₁_ge, hx₁_le, hfx₁⟩ :=
    exact_ivt_on_interval hIVT 0 c hc0_lt f hf_cont hf0 hfc
  -- Apply IVT on [c, 1]: f(c) > 0 > f(1), get x₂ with f(x₂) = 0
  obtain ⟨x₂, hx₂_ge, hx₂_le, hfx₂⟩ :=
    exact_ivt_on_interval_neg hIVT c 1 hc1_lt f hf_cont hfc hf1
  -- Construct TurningPoints
  have h_x₁_root : B.V x₁ = B.E := by simp [hf_def] at hfx₁; linarith
  have h_x₂_root : B.V x₂ = B.E := by simp [hf_def] at hfx₂; linarith
  have h_order : x₁ < x₂ := by
    by_contra h
    push_neg at h
    -- x₂ ≤ x₁, but x₁ ≤ c and x₂ ≥ c, so c ≤ x₂ ≤ x₁ ≤ c
    -- This forces x₁ = c = x₂, but f(c) > 0 ≠ 0 = f(x₁)
    have : x₁ = c := le_antisymm hx₁_le (le_trans hx₂_ge h)
    rw [this] at hfx₁
    simp [hf_def] at hfx₁
    linarith
  exact ⟨⟨x₁, x₂,
    ⟨hx₁_ge, le_trans hx₁_le (le_of_lt hc1_lt)⟩,
    ⟨le_trans (le_of_lt hc0_lt) hx₂_ge, hx₂_le⟩,
    h_x₁_root, h_x₂_root, h_order⟩⟩

-- ========================================================================
-- Forward direction: TPP → ExactIVT
-- ========================================================================

/-- TPP implies ExactIVT.
    Given f continuous with f(0) < 0 < f(1), construct a barrier whose
    turning point gives a root of f.

    Construction: Define V(x) = -f(2x) for x ∈ [0, 1/2] (rescaled),
    V(x) = -f(2-2x) for x ∈ [1/2, 1] (reflected). Then V is a barrier
    with E = 0, and a turning point gives a root of f.

    Simplified approach: we construct a barrier directly from f by
    using V(x) = -f(x) and adjusting the domain. -/
theorem ivt_of_tpp (hTPP : TPP) : ExactIVT := by
  intro f hf_cont hf0 hf1
  -- Strategy: construct a barrier from f using reflection.
  -- V(x) = f(2x) for x ≤ 1/2, V(x) = f(2-2x) for x > 1/2
  -- Then V(0) = f(0) < 0, V(1/2) = f(1) > 0, V(1) = f(0) < 0
  -- Set E = 0. A turning point x₁ gives a root of f.

  -- Define the two branches
  let g₁ : ℝ → ℝ := fun x => f (2 * x)
  let g₂ : ℝ → ℝ := fun x => f (2 - 2 * x)
  have hg₁_cont : Continuous g₁ := hf_cont.comp (continuous_const.mul continuous_id')
  have hg₂_cont : Continuous g₂ := hf_cont.comp (continuous_const.sub (continuous_const.mul continuous_id'))

  -- V defined as piecewise
  set V : ℝ → ℝ := fun x => if x ≤ 1/2 then g₁ x else g₂ x with hV_def

  -- V is continuous
  have hV_cont : Continuous V := by
    apply Continuous.if_le
    · exact hg₁_cont
    · exact hg₂_cont
    · exact continuous_id'
    · exact continuous_const
    · intro x hx
      show g₁ x = g₂ x
      simp only [g₁, g₂]
      congr 1; linarith

  -- Key values
  have hV0 : V 0 < 0 := by
    simp only [hV_def, show (0:ℝ) ≤ 1/2 from by norm_num, ite_true, g₁]
    simp; exact hf0
  have hV_half : V (1/2) > 0 := by
    simp only [hV_def, show (1/2:ℝ) ≤ 1/2 from le_refl _, ite_true, g₁]
    show f (2 * (1/2)) > 0
    norm_num; exact hf1
  have hV1 : V 1 < 0 := by
    simp only [hV_def, show ¬((1:ℝ) ≤ 1/2) from by norm_num, ite_false, g₂]
    show f (2 - 2 * 1) < 0
    norm_num; exact hf0

  -- Build barrier with E = 0
  set B : Barrier := {
    V := V
    hV_cont := hV_cont
    E := 0
    h_left := hV0
    h_peak := ⟨1/2, by norm_num, by norm_num, hV_half⟩
    h_right := hV1
  }

  -- Apply TPP
  obtain ⟨tp⟩ := hTPP B
  -- tp.h_left_root : B.V tp.x₁ = B.E, i.e., V(x₁) = 0
  have hroot : V tp.x₁ = 0 := tp.h_left_root
  -- Extract a root of f from the turning point
  by_cases hx₁_half : tp.x₁ ≤ 1/2
  · -- V(x₁) = g₁(x₁) = f(2x₁) = 0
    have hV_eq : V tp.x₁ = f (2 * tp.x₁) := by
      simp only [hV_def, hx₁_half, ite_true, g₁]
    refine ⟨2 * tp.x₁, ?_, ?_, ?_⟩
    · linarith [tp.h_x₁_range.1]
    · linarith
    · linarith
  · -- V(x₁) = g₂(x₁) = f(2 - 2x₁) = 0
    push_neg at hx₁_half
    have hV_eq : V tp.x₁ = f (2 - 2 * tp.x₁) := by
      simp only [hV_def, show ¬(tp.x₁ ≤ 1 / 2) from not_le.mpr hx₁_half, ite_false, g₂]
    refine ⟨2 - 2 * tp.x₁, ?_, ?_, ?_⟩
    · linarith [tp.h_x₁_range.2]
    · linarith
    · linarith

-- ========================================================================
-- Main equivalence: TPP ↔ LLPO
-- ========================================================================

/-- Theorem 4: The Turning Point Problem is equivalent to LLPO.
    TPP ↔ ExactIVT ↔ LLPO. -/
theorem turning_point_problem_iff_llpo : TPP ↔ LLPO := by
  constructor
  · -- TPP → LLPO
    intro hTPP
    rw [← exact_ivt_iff_llpo]
    exact ivt_of_tpp hTPP
  · -- LLPO → TPP
    intro hLLPO
    have hIVT := exact_ivt_iff_llpo.mpr hLLPO
    exact tpp_of_ivt hIVT

end Papers.P19
end
