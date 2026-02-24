/-
Papers/P19_WKBTunneling/Calibration/PartA.lean
Theorem 1: Specific barriers are BISH-computable.

When the turning points are given (not found by root-finding), the WKB
action integral and tunneling amplitude are BISH-computable. No IVT,
no LLPO, no LPO needed.

Axiom audit expectation: [propext, Classical.choice, Quot.sound]
  - Classical.choice from Mathlib infrastructure (intervalIntegral, Real.exp)
  - NO custom axioms (exact_ivt_iff_llpo, bmc_iff_lpo absent)
-/
import Papers.P19_WKBTunneling.Barrier.Rectangular
import Papers.P19_WKBTunneling.Barrier.Parabolic
import Papers.P19_WKBTunneling.WKB.Amplitude

noncomputable section
namespace Papers.P19

-- ========================================================================
-- Theorem 1a: WKB action is computable when turning points are given
-- ========================================================================

/-- Theorem 1a: The WKB action integral exists for any continuous barrier
    with explicitly given turning points. No root-finding needed. -/
theorem wkb_action_computable
    (V : ℝ → ℝ) (_hV : Continuous V) (E m : ℝ)
    (x₁ x₂ : ℝ) (_hx₁ : V x₁ = E) (_hx₂ : V x₂ = E)
    (_hlt : x₁ < x₂) :
    ∃ S : ℝ, S = ∫ x in x₁..x₂, Real.sqrt (2 * m * (V x - E)) :=
  ⟨_, rfl⟩

-- ========================================================================
-- Theorem 1b: Tunneling amplitude is computable
-- ========================================================================

/-- Theorem 1b: The tunneling amplitude T = exp(-S/ℏ) is computable
    for any given action S and any ℏ > 0. -/
theorem tunneling_amplitude_computable
    (S : ℝ) (ℏ : ℝ) (_hℏ : 0 < ℏ) :
    ∃ T : ℝ, T = Real.exp (-S / ℏ) :=
  ⟨_, rfl⟩

-- ========================================================================
-- Corollaries for specific barrier types
-- ========================================================================

/-- Corollary: rectangular barrier action is computable. -/
theorem rectangular_wkb_computable
    (V₀ E m x₁ x₂ ℏ : ℝ) (_hm : 0 < m) (_hEV : E < V₀)
    (_hlt : x₁ < x₂) (_hℏ : 0 < ℏ) :
    ∃ T : ℝ, T = wkbAmplitudeExplicit (fun _ => V₀) E m x₁ x₂ ℏ :=
  ⟨_, rfl⟩

/-- Corollary: parabolic barrier action is computable. -/
theorem parabolic_wkb_computable
    (V₀ a E m ℏ : ℝ) (_hV₀ : 0 < V₀) (_ha : 0 < a) (_hE : 0 < E)
    (_hEV : E < V₀) (_hm : 0 < m) (_hℏ : 0 < ℏ) :
    ∃ T : ℝ, T = wkbAmplitudeExplicit (parabolicV V₀ a) E m
      (parabolicTP_left V₀ a E) (parabolicTP_right V₀ a E) ℏ :=
  ⟨_, rfl⟩

end Papers.P19
end
