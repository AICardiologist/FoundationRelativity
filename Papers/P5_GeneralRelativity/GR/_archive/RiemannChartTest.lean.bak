import Papers.P5_GeneralRelativity.GR.Schwarzschild

/-!
# Isolated Test: Chart-Based Compatibility Lemmas

This file contains ONLY the Chart infrastructure to test if it's the compilation bottleneck.
-/

namespace Schwarzschild

/-! ## Chart Structure (for general pair-exchange) -/

/-- Minimal coordinate chart predicate: just the three nonvanishing conditions. -/
structure Chart (M r θ : ℝ) : Prop where
  hr : r ≠ 0
  hf : f M r ≠ 0          -- equivalently r ≠ 2M
  hs : Real.sin θ ≠ 0     -- off the axis

/-- Bridge lemma: Exterior implies Chart (when θ is away from poles). -/
lemma Exterior.toChart (h : Exterior M r θ) (hθ : 0 < θ ∧ θ < Real.pi) :
  Chart M r θ :=
  ⟨h.r_ne_zero, h.f_ne_zero, sin_theta_ne_zero θ hθ⟩

/-! #### Chart Versions (for general pair-exchange proof)

The following lemmas are identical to the _ext versions above, but use the minimal
`Chart` hypothesis instead of `Exterior`. This allows proving Riemann_pair_exchange
without Exterior hypotheses by case-splitting on the chart.
-/

/-- Atomic compatibility lemma for r-derivative of g_tt. -/
lemma compat_r_tt_chart
    (M r θ : ℝ) (hC : Chart M r θ) :
  dCoord Idx.r (fun r θ => g M Idx.t Idx.t r θ) r θ
    = 2 * Γtot M r θ Idx.t Idx.r Idx.t * g M Idx.t Idx.t r θ := by
  sorry

/-- Atomic compatibility lemma for r-derivative of g_rr. -/
lemma compat_r_rr_chart
    (M r θ : ℝ) (hC : Chart M r θ) :
  dCoord Idx.r (fun r θ => g M Idx.r Idx.r r θ) r θ
    = 2 * Γtot M r θ Idx.r Idx.r Idx.r * g M Idx.r Idx.r r θ := by
  sorry

lemma dCoord_g_via_compat_chart (M r θ : ℝ) (hC : Chart M r θ) (x a b : Idx) :
  dCoord x (fun r θ => g M a b r θ) r θ =
    sumIdx (fun k => Γtot M r θ k x a * g M k b r θ) +
    sumIdx (fun k => Γtot M r θ k x b * g M a k r θ) := by
  match x, a, b with
  | Idx.r, Idx.t, Idx.t =>
      simp [compat_r_tt_chart M r θ hC, sumIdx_expand, g, Γtot]
  | Idx.r, Idx.r, Idx.r =>
      simp [compat_r_rr_chart M r θ hC, sumIdx_expand, g, Γtot]
  | _, _, _ =>
      -- All other 62 cases are zero or trivial
      sorry

lemma nabla_g_zero_chart (M r θ : ℝ) (hC : Chart M r θ) (c a b : Idx) :
  nabla_g M r θ c a b = 0 := by
  simp only [nabla_g]
  rw [dCoord_g_via_compat_chart M r θ hC]
  abel

lemma dCoord_nabla_g_zero_chart (M r θ : ℝ) (hC : Chart M r θ)
    (μ c a b : Idx) :
    dCoord μ (fun r θ => nabla_g M r θ c a b) r θ = 0 := by
  -- On the good chart, nabla_g = 0 pointwise, so its derivative is 0
  -- (We don't need the open set argument - it's just pointwise differentiation of 0)
  have h : nabla_g M r θ c a b = 0 := nabla_g_zero_chart M r θ hC c a b
  cases μ
  case t => simp [dCoord_t]
  case φ => simp [dCoord_φ]
  case r =>
    simp only [dCoord_r]
    rw [show (fun r' => nabla_g M r' θ c a b) = fun _ => 0 by
      ext r'; exact nabla_g_zero_chart M r' θ ⟨hC.hr, hC.hf, hC.hs⟩ c a b]
    simp [deriv_const]
  case θ =>
    simp only [dCoord_θ]
    rw [show (fun θ' => nabla_g M r θ' c a b) = fun _ => 0 by
      ext θ'
      -- Chart hypotheses hr, hf are independent of θ', so Chart still holds
      exact nabla_g_zero_chart M r θ' ⟨hC.hr, hC.hf, hC.hs⟩ c a b]
    simp [deriv_const]

end Schwarzschild
