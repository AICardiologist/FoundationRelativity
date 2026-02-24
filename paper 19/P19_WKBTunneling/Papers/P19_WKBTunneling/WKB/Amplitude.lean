/-
Papers/P19_WKBTunneling/WKB/Amplitude.lean
WKB tunneling amplitude: T = exp(-S/ℏ)

The tunneling amplitude is an exponentially decreasing function of the
action integral divided by ℏ. For ℏ > 0 and S ≥ 0, we have 0 < T ≤ 1.
-/
import Papers.P19_WKBTunneling.WKB.Action

noncomputable section
namespace Papers.P19

-- ========================================================================
-- WKB tunneling amplitude
-- ========================================================================

/-- WKB tunneling amplitude: T = exp(-S/ℏ). -/
def wkbAmplitude (B : Barrier) (tp : TurningPoints B) (m ℏ : ℝ) : ℝ :=
  Real.exp (-(wkbAction B tp m) / ℏ)

/-- The tunneling amplitude is always positive (exp is positive). -/
lemma wkbAmplitude_pos (B : Barrier) (tp : TurningPoints B) (m ℏ : ℝ) :
    0 < wkbAmplitude B tp m ℏ :=
  Real.exp_pos _

/-- Alternative form: amplitude for explicit parameters. -/
def wkbAmplitudeExplicit (V : ℝ → ℝ) (E m x₁ x₂ ℏ : ℝ) : ℝ :=
  Real.exp (-(wkbActionExplicit V E m x₁ x₂) / ℏ)

/-- Explicit amplitude is positive. -/
lemma wkbAmplitudeExplicit_pos (V : ℝ → ℝ) (E m x₁ x₂ ℏ : ℝ) :
    0 < wkbAmplitudeExplicit V E m x₁ x₂ ℏ :=
  Real.exp_pos _

end Papers.P19
end
